-- Prove2me | Theorems.Thm_WeightedSpectralSketch_LowerBound_lifting
-- name    : WeightedSpectralSketch.LowerBound.lifting
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:14:43.405927+00:00
-- url     : https://prove2.me/theorems/a12e1b25-5d77-4d7f-8bbe-c9684a78c288
-- title:
--   Lemma 6.4 — lifting an incidence representation with bounded anchor residual
-- statement:
--   Fix an anchor set $C$ and the ring $R=V\setminus C$, and let $B=[b_e:e\in\binom R2]$, $T$ and $(c_e)$ be as supplied by Lemma 6.3, i.e. satisfying its conclusions (1) $a_e=Tb_e+A_Cc_e$, $\|c_e\|_2^2\le3$ on anchor-good ring edges and (2) $b_e=0$, $c_e=0$ on the others. Let $q\in\binom R2$ be any anchor-good ring edge, and suppose $f=(f_e)_{e\ne q}$ satisfies $b_q=\sum_{e\ne q}f_eb_e$ and $f_e=0$ whenever $b_e=0$. Then there is $c\in\mathbb R^{\binom C2}$ with
--
--   $$
--   a_q=\sum_{e\in\binom R2\setminus\{q\}}f_ea_e+A_Cc \tag{16}
--   $$
--
--   and
--
--   $$
--   \|c\|_2^2\le6\big(1+|R|^2\|f\|_2^2\big)\qquad(|R|=\ell b\text{ in the source}).
--   $$
--
--   Because $T$ is common to all columns, a cheap representation of $b_q$ lifts to one of $a_q$ plus an anchor residual whose weighted cost is negligible against the heavy anchor weights.
--
--   Differences from the source:
--
--   - generalization: B, T, (c_e) the matrices supplied by Lemma 6.3 for a realization of the anchored template, and ℓ²b² = |R|² → any K, B, T, (c_e) satisfying conclusions (1)–(2) of Lemma 6.3, for any anchor set C, with |R|² in the bound; reason: the source's B, T, (c_e) satisfy (1)–(2), and |R| = ℓb there; the proof uses only (1)–(2)
-- source:
--   Chen, Chen and Yang, A Tight Superlinear Lower Bound on the Sketching Dimension of Weighted Spectral Sparsification, STOC 2027 submission #109 (2026), pinned preprint SHA-256 94f9d972f8c75c577e7195e080b6ed59e722471145d40426a2f0c92315be9f44, p. 24, Lemma 6.4, Eq. (16), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/109.pdf

import Mathlib
import Definitions.Def_WeightedSpectralSketch_LowerBound_Graph
import Definitions.Def_WeightedSpectralSketch_LowerBound_Anchor

open Matrix

namespace WeightedSpectralSketch.LowerBound

/-- Lemma 6.4, p. 24 (lifting): fix `C` and the ring `R = V \ C`, and let `B`, `T`, `(c_e)` satisfy
the conclusions (1)–(2) of Lemma 6.3. Let `q` be an anchor-good ring edge and `f = (f_e)_{e ≠ q}`
with `b_q = ∑_{e ≠ q} f_e b_e` and `f_e = 0` whenever `b_e = 0`. Then there is `c ∈ ℝ^{binom(C,2)}`
with `a_q = ∑_{e ≠ q} f_e a_e + A_C c` (16) and `‖c‖₂² ≤ 6 (1 + |R|² ‖f‖₂²)` (`|R| = ℓ b`). -/
theorem lifting {V : Type*} [Fintype V] [DecidableEq V] {N K : ℕ}
    (A : Matrix (Fin N) (EdgeSlot V) ℝ) (C : Finset V)
    (B : Matrix (Fin K) (EdgeSlot {v // v ∉ C}) ℝ) (T : Matrix (Fin N) (Fin K) ℝ)
    (c : EdgeSlot {v // v ∉ C} → anchorEdges C → ℝ)
    (h1 : ∀ e, AnchorGood A C (liftEdge C e).1 →
      Aᵀ (liftEdge C e) = T *ᵥ Bᵀ e + anchorMat A C *ᵥ c e ∧ ∑ k, c e k ^ 2 ≤ 3)
    (h2 : ∀ e, ¬ AnchorGood A C (liftEdge C e).1 → Bᵀ e = 0 ∧ c e = 0)
    (q : EdgeSlot {v // v ∉ C}) (hq : AnchorGood A C (liftEdge C q).1)
    (f : {e : EdgeSlot {v // v ∉ C} // e ≠ q} → ℝ) (hrep : Bᵀ q = ∑ e, f e • Bᵀ e.1)
    (hf : ∀ e, Bᵀ e.1 = 0 → f e = 0) :
    ∃ c' : anchorEdges C → ℝ,
      Aᵀ (liftEdge C q) = ∑ e, f e • Aᵀ (liftEdge C e.1) + anchorMat A C *ᵥ c' ∧
      ∑ k, c' k ^ 2 ≤ 6 * (1 + (Fintype.card {v // v ∉ C} : ℝ) ^ 2 * ∑ e, f e ^ 2) := by sorry

end WeightedSpectralSketch.LowerBound
