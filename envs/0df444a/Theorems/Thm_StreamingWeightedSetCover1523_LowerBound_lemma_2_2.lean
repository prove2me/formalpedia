-- Prove2me | Theorems.Thm_StreamingWeightedSetCover1523_LowerBound_lemma_2_2
-- name    : StreamingWeightedSetCover1523.LowerBound.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:08:07.769224+00:00
-- url     : https://prove2.me/theorems/4f57a29c-33f0-494f-8d0b-66530022a376
-- title:
--   Lemma 2.2 — repairable masks and the entropy certificate (9)
-- statement:
--   1. For every $v,M,k$ and every matrix $A$, every mask $z$ in the support of $\mu_A$ is repairable by at most $k$ cheap sets: there is $K\subseteq[M]$ with $|K|\le k$ such that every coordinate $e$ with $z_e=1$ lies in some $A_j$, $j\in K$.
--
--   2. There is an absolute constant $C_0>0$ such that for all sequences $\alpha(k)$, $M(k)$, $v(k)$ satisfying the regime (1) with this $C_0$, for all sufficiently large $k$, with probability at least $9/10$ over the draw of $A$ (independent Bernoulli$(4/k)$ entries) both properties hold: the cheap family covers $U$, and for every pair of densities $f,g:\mathbb F_2^v\to\mathbb R_{\ge0}$
--   $$\mathbb E_{X\sim U_v,\,Z\sim\mu_A}f(X)\,g(1+X+Z)\ \ge\ 1-\varepsilon-\frac{120}{d}\big(\mathrm{Ent}(f)+\mathrm{Ent}(g)\big).\qquad(9)$$
--
--   The densities may be chosen after $A$ is revealed: the inequality is required for all pairs inside the good event. This certificate is what hides the planted pair from tests that see the public cheap matrix.
--
--   Differences from the source:
--   - generalization: support statement for the fixed parameters of §2 → support statement for all v, M, k; reason: it uses only h(0) = 1, valid for every k; specializes to the source parameters
--   - encoding: "for sufficiently large C₀ and k", v = o(k²), integers M, v → ∃ C₀ > 0 before all sequences α, M, v : ℕ → ℝ/ℕ; ∀ᶠ k in atTop; v = o(k²) as Asymptotics.IsLittleO; reason: the standing regime of §2 (PDF pp. 7, 11) and Appendix A.2 (PDF p. 22); (1) forces M, v positive on the tail
--   - generalization: parameters satisfying (1) (for every k) → (1) and α ≥ 1 required only for all sufficiently large k; reason: the conclusion is asymptotic in k; sequences satisfying (1) for every k satisfy it eventually
--   - encoding: probability over the draw of A with independent Bernoulli(4/k) entries → probA: the finite sum of the product weights ∏(4/k or 1−4/k) over the matrices in the event; reason: the exact law of A on the finite set of matrices
--   - encoding: d = ⌊k²/(64ev)⌋, 120/d → Nat.floor and real division (x/0 = 0); reason: d ≥ 1 for all large k in the regime (1), where the statement is asserted
--   - encoding: vectors in F₂^v, a v×M binary matrix, U=[v]×{0,1}, identifiers C_1..C_M, E_1..E_M, indices 1..M → Fin v → ZMod 2, Fin v → Fin M → Bool, Fin v × ZMod 2, Fin M ⊕ Fin M, 0-based indices (left block = indices 0..r−1); reason: finite relabelling of the same objects; no instance changes
-- source:
--   Ali Vakilian, Streaming Weighted Set Cover Requires (Nearly) Linear Space, STOC 2027 submission #1523 (October 2026), Lemma 2.2, printed p. 10 (PDF p. 11), eq. (9); regime from §2.4 (PDF p. 11) and Appendix A (PDF pp. 19–22); citation basis: submitted artifact, sha256 16f3c2dfc6183f4752aece654f17f2cb6a47fbe55659e6906ad7bd3524d6223f

import Definitions.Def_StreamingWeightedSetCover1523_LowerBound_HardInstance

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal

namespace StreamingWeightedSetCover1523.LowerBound

/-- Lemma 2.2 (PDF p. 11, eq. (9)): (i) for every `A`, every mask in the support of `μ_A` is
repairable by at most `k` cheap sets; (ii) there is an absolute `C₀ > 0` such that for all
parameter sequences satisfying (1), for all sufficiently large `k`, with probability at least
`9/10` over the initial draw of `A`, the cheap family covers `U` and (9) holds for every pair of
densities (`Good`). -/
theorem lemma_2_2 :
    (∀ (v M k : ℕ) (A : Mat v M) (z : Vec v), mu k A z ≠ 0 →
      ∃ K : Finset (Fin M), K.card ≤ k ∧ ∀ e : Fin v, z e = 1 → ∃ j ∈ K, A e j = true) ∧
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (α : ℕ → ℝ) (M v : ℕ → ℕ), ParamsEq1 C₀ α M v →
        ∀ᶠ k : ℕ in atTop, (9 / 10 : ℝ) ≤ probA k (fun A : Mat (v k) (M k) => Good k A) := by sorry

end StreamingWeightedSetCover1523.LowerBound
