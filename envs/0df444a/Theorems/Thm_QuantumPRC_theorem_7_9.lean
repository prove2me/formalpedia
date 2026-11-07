-- Prove2me | Theorems.Thm_QuantumPRC_theorem_7_9
-- name    : QuantumPRC.theorem_7_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:38:44.265199+00:00
-- url     : https://prove2.me/theorems/908e0de6-8825-48c1-af1a-07b392260bdc
-- title:
--   Theorem 7.9 — PF isometries are $O(t^2/2^\ell)$-indistinguishable from Haar isometries
-- statement:
--   There is a constant $C$ such that for all integers $n_{\mathrm L},\ell,s,t$, with $n_{\mathrm P}=n_{\mathrm L}+\ell+s$, and every oracle circuit $\mathcal A$ making at most $t$ queries to an oracle from $n_{\mathrm L}$ to $n_{\mathrm P}$ qubits,
--
--   $$
--   \Big|\Pr_{\pi',f'}\big[1\leftarrow\mathcal A^{V_{\pi',f'}}\big]-\Pr_{V\leftarrow\mu_{n_{\mathrm L}\to n_{\mathrm P}}}\big[1\leftarrow\mathcal A^{V}\big]\Big|\le C\,\frac{t^2}{2^\ell},
--   $$
--
--   where $V_{\pi',f'}|x\rangle=2^{-\ell/2}\sum_{y\in\{0,1\}^\ell}(-1)^{f'(x\|y)}|\pi'(x\|y\|0^s)\rangle$ (167), $\pi'$ is a uniformly random permutation of $\{0,1\}^{n_{\mathrm P}}$ and $f'$ a uniformly random function $\{0,1\}^{n_{\mathrm L}+\ell}\to\{0,1\}$. The adversary's size is not bounded.
--
--   This statistical statement (adapted from [MPSY24, Theorem 6.2]) is the step from PF isometries to Haar isometries in the pseudorandomness proof (176).
--
--   Differences from the source:
--   - reading: for any t-query adversary A, … ≤ O(t²/2^ℓ) → one constant C for all nL, ℓ, s, t and all oracle circuits with at most t queries; reason: the meaning of O(·) in a statement quantified over all parameters; 'at most t' and 'exactly t' agree since the bound is monotone in t
--   - encoding: the Haar measure µ_{nL→nP} on isometries → V = U·ι with U Haar-distributed on U(2^{nP}) and ι|x⟩ = |x⟩|0^{nP−nL}⟩; reason: the realization used on p.69; it is the left- and right-invariant measure on isometries
-- source:
--   Hsieh, Yamada, Quantum Pseudorandom Error-Correcting Codes, arXiv:2609.38986 (version of October 29, 2026, sha256 6901b59d1cbcf0183f98f2951ab17c9baae4e341e5b2a3c767d1ae93e77976db), Theorem 7.9, Eqs. (167)–(168), p.49 (adapted from [MPSY24, Theorem 6.2])

import Mathlib
import Definitions.Def_QuantumPRC_ChScheme
import Definitions.Def_QuantumPRC_pfIso

namespace QuantumPRC

/-- **Theorem 7.9** (PF isometries versus Haar isometries; adapted from Theorem 6.2 of [MPSY24]).
Hsieh, Yamada, arXiv:2609.38986 (sha256 6901b59d…), Theorem 7.9, p.49: "Let `nL`, `ℓ`, and `s` be integers,
and define `nP := nL + ℓ + s`. For a permutation `π′` over `nP` bits and a function `f′ : {0,1}^{nL+ℓ} → {0,1}`,
define an isometry from `nL` qubits to `nP` qubits by `V_{π′,f′} : |x⟩ ↦ (1/√2^ℓ) Σ_{y∈{0,1}^ℓ} (−1)^{f′(x∥y)}
|π′(x∥y∥0^s)⟩`. Then, for any `t`-query adversary `A`, `|Pr_{π′,f′}[1 ← A^{V_{π′,f′}}] − Pr_{V←µ_{nL→nP}}[1 ← A^V]| ≤
O(t²/2^ℓ)`, where `π′` and `f′` are chosen uniformly at random."

**Formalization Note.** `O(·)` is one constant `C` for all `nL, ℓ, s, t` and all adversaries; a
`t`-query adversary is any oracle circuit (no size bound) with at most `t` queries; the Haar isometry is
`U·ι` with `U` Haar on `U(2^{nP})`. -/
theorem theorem_7_9 :
    ∃ C : ℝ, ∀ (nL ℓ s t : ℕ) (A : OCirc nL (nL + ℓ + s) 1), A.numQueries ≤ t →
      |avg (fun π' : Equiv.Perm (Bits (nL + ℓ + s)) => avg fun f' : Bits (nL + ℓ) → Bool =>
          A.accept (fun _ => conjMap (pfIso π' f')) []) -
        ∫ U, A.accept (fun _ => conjMap (haarIsoMat nL (nL + ℓ + s) U)) []
          ∂(QAlgorithms.Schur.unitaryHaar (2 ^ (nL + ℓ + s)))| ≤ C * (t : ℝ) ^ 2 / 2 ^ ℓ := by sorry

end QuantumPRC
