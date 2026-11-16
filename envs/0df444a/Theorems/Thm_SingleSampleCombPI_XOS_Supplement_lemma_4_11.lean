-- Prove2me | Theorems.Thm_SingleSampleCombPI_XOS_Supplement_lemma_4_11
-- name    : SingleSampleCombPI.XOS.Supplement.lemma_4_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:46:12.193319+00:00
-- url     : https://prove2.me/theorems/c5e45bde-3a91-4ed2-8d06-76c3d800d623
-- title:
--   Lemma 4.11 — Every final buyer/allocation dual constraint
-- statement:
--   For any valid full Algorithm 6 trace with DR-submodular concave valuations, its final dual vector satisfies every constraint
--   $$\beta_i+\langle x,\alpha^{(n)}\rangle\ge v_i(x)\qquad(i\in[n],\ x\in[0,1]^m).$$
--   Each $\beta_i$ uses the actual post-update prices at the arrival of buyer $i$, while $\alpha^{(n)}$ is computed from the full final history. Arrival orders are arbitrary.
--
--   Differences from the source:
--   - encoding: twice-differentiable DR-submodular concave valuations on the nonnegative orthant and Algorithm 6 → within-orthant first/second Frechet derivatives, antitone gradient, canonical Aumann–Shapley prices and reachable frozen-history transitions; reason: these are Definition 6 and Proposition 2.2 conventions; C² regularity, Lipschitz constants and arbitrary supplied supporting maps are not assumed
--   - encoding: valid states, traces and arbitrary arrival order → inductively reachable histories and explicit order-indexed frozen records; reason: only initialization and actual Condition 1 transitions are assumed; no lemma conclusion or unproved algorithmic invariant is a state field
-- source:
--   Shuchi Chawla, Trung Dang, STOC 2027 submission #30 (October 2026), Lemma 4.11, printed p. 26 / PDF p. 28; proof printed 26 / PDF 28.

import Mathlib
import Definitions.Def_SingleSampleCombPI_XOS_Supplement_GreedyDR

namespace SingleSampleCombPI.XOS.Supplement

/-- Lemma 4.11, PDF 28 / printed 26. All buyer/allocation constraints
at the final dual vector; no constraint is assumed as an invariant. -/
theorem lemma_4_11 {n m : ℕ} (v : Fin n → Vec m → ℝ)
    (hv : ∀ i, DRConcave (v i)) (ρ : Equiv.Perm (Fin n)) (x : Fin n → Cube m)
    (hx : A6Trace v ρ x) : ∀ i, ∀ y : Cube m,
    v i y.1 ≤ a6Beta v ρ x i + dot (a6Alpha (a6History v ρ x n)) y.1 := by sorry

end SingleSampleCombPI.XOS.Supplement
