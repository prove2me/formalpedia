-- Prove2me | Theorems.Thm_SpaceReset_Hardness_Supplement_lemma_21
-- name    : SpaceReset.Hardness.Supplement.lemma_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T13:41:24.442887+00:00
-- url     : https://prove2.me/theorems/704538a3-b903-43ad-a04b-ad7da10dcbce
-- title:
--   Lemma 21 — spectrum bound from deterministic outputs
-- statement:
--   Fix an online instrument with $N$ slots, given as a target process whose initial memory state is a state and whose slot maps are channels, and fix a cut $t\le N$. Suppose:
--
--   1. $2^L$ distinct computational-basis inputs $x$ for the slots before the cut, each completed by one common computational-basis input $y$ for the slots after the cut, produce a pure joint state $|o_x\rangle\langle o_x|$ of the outputs returned before the cut;
--   2. some POVM $\{F_x\}$ on the outputs returned after the cut identifies $x$ with probability one;
--   3. the normalized Choi state $J$ of the instrument is flat of rank $2^k$: $J^2=2^{-k}J$ and $\operatorname{rank}J=2^k$.
--
--   Let an implementation have integer budgets $q,g$, any initializer $\sigma$, and operational error at most $\varepsilon$, where $0\le\varepsilon<1/4$, against adaptive testers. Then
--   $$q\ge L,\qquad 2(q+g)\ge k+L,$$
--   and some $2^{q+g-L}$ eigenvalues of $\sigma$, counted with multiplicity, carry total weight at least $1-\varepsilon$. Equivalently, at least $1-\varepsilon$ of the initializer mass lies in its largest $2^{q+g-L}$ eigenvalues.
--
--   This spectral bound is the converse half of Theorem 20: for $\mathcal P_m$ it gives $L=m$ and $k=2m$.
--
--   Differences from the source:
--   - encoding: an online instrument with arbitrary input and output registers → a target online process with register families I, O indexed by ℕ (0-based slots), initial memory state a state and slot maps channels on the N used slots; reason: every causal instrument has such a memory realization, and only its input–output behaviour enters
--   - encoding: operational error = trace distance maximized over adaptive input/reference testers → for every valid adaptive tester and every slot j < N, the trace distance of the tester states right after slot j is at most ε; reason: a tester can carry any earlier state to the end in its reference and a final channel only contracts trace distance, so this equals the bound on the final state
--   - encoding: 2^L computational prefix inputs x with ideal pure past output |o_x⟩ → an injective family x : Fin (2^L) → basis strings on the slots < t, each completed by the common suffix input y, whose past-output marginal is vecMulVec v (star v) for some vector v; reason: by causality the past outputs do not depend on the later inputs
--   - encoding: a common fixed suffix input reveals x from future outputs alone → a POVM F on the outputs of slots ≥ t with Tr(F_a ρ_a) = 1 for the future-output marginal ρ_a of the run on (x a, y); reason: identification with probability one
--   - encoding: complete instrument Choi state flat of rank 2^k → J * J = 2^{-k} J and rank J = 2^k for the normalized Choi state J; reason: J is positive semidefinite, so J² = 2^{-k} J says every nonzero eigenvalue equals 2^{-k}
--   - encoding: at least 1 − ε of the initializer mass lies in its largest 2^{q+g−L} eigenvalues → some set of at most 2^{q+g−L} eigenvalue indices of σ has eigenvalue sum ≥ 1 − ε; reason: eigenvalues are nonnegative, so the best such set is the top 2^{q+g−L}; q + g − L is not truncated because q ≥ L is the first conclusion
--   - encoding: operational error ε < 1/4 → 0 ≤ ε < 1/4; reason: an operational error is a trace distance, hence nonnegative; 0 ≤ ε excludes only values the source never considers (with N = 0 slots and ε < 0 the last conclusion would be false)
-- source:
--   Rinka Miura, STOC 2027 submission #1715 (October 2026), The Complexity of Space–Reset Tradeoffs in Online Quantum Computation (held submission, no arXiv version; SHA-256 c2a340e2195da0d130bf10d936d56d4f1d4da805e644efb7fe1c36d9c904f3e5), Lemma 21, p. 30 (setting §4, p. 29; proof pp. 30–31)

import Mathlib
import Definitions.Def_SpaceReset_Hardness_Supplement_Online

set_option autoImplicit false

namespace SpaceReset.Hardness.Supplement

open Matrix SpaceReset.Hardness
open scoped ComplexOrder

/-- Lemma 21 (Spectrum bound from deterministic outputs), §4.1, p. 30.

A target online instrument (initial memory state a state, every used slot map a channel) with register families `I`, `O` over `N` slots and a cut `t`.
The `2^L` distinct computational-basis past inputs `x a` (slots `< t`), each completed by one
common computational-basis future input `y` (slots `≥ t`), give a pure joint state of the past
outputs, and a POVM `F` on the future outputs identifies `a` with probability one. The normalized
Choi state of the target is flat of rank `2^k` (all nonzero eigenvalues equal `2^{-k}`). Then
every implementation with integer budgets `q, g` (any initializer `σ`) whose operational error is
at most `ε`, `0 ≤ ε < 1/4`, has `q ≥ L`, `2(q + g) ≥ k + L`, and some `2^{q+g−L}` eigenvalues of `σ`
(counted with multiplicity) carry total weight at least `1 − ε`. -/
theorem lemma_21 (I O : ℕ → Type) [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
    (N : ℕ) (Tgt : OProcess I O) (hTgt : IsDensity Tgt.σ ∧ ∀ j < N, IsChannel (Tgt.Φ j)) (t : ℕ) (ht : t ≤ N) (L k : ℕ)
    (x : Fin (2 ^ L) → ((j : {j : Fin N // j.val < t}) → I j)) (hx : Function.Injective x)
    (y : (j : {j : Fin N // ¬ j.val < t}) → I j)
    (hpure : ∀ a, ∃ v : ((j : {j : Fin N // j.val < t}) → O j) → ℂ,
      pastMarginal t (basisRun N Tgt (joinInputs (x a) y)) = vecMulVec v (star v))
    (F : Fin (2 ^ L) → Matrix ((j : {j : Fin N // ¬ j.val < t}) → O j)
      ((j : {j : Fin N // ¬ j.val < t}) → O j) ℂ)
    (hF : IsPOVM F)
    (hdec : ∀ a, (F a * futureMarginal t (basisRun N Tgt (joinInputs (x a) y))).trace = 1)
    (hflat : choiState N Tgt * choiState N Tgt = ((2 : ℂ) ^ k)⁻¹ • choiState N Tgt ∧
      (choiState N Tgt).rank = 2 ^ k)
    (q g : ℕ) (ε : ℝ) (hε0 : 0 ≤ ε) (hε : ε < 1 / 4) (D : ODevice I O N q g)
    (hD : OErrorLE N D.toProcess Tgt ε) :
    L ≤ q ∧ k + L ≤ 2 * (q + g) ∧
      ∃ S : Finset D.M, S.card ≤ 2 ^ (q + g - L) ∧
        1 - ε ≤ ∑ i ∈ S, D.σ_density.1.isHermitian.eigenvalues i := by sorry

end SpaceReset.Hardness.Supplement
