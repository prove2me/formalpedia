-- Prove2me | Theorems.Thm_RegevRecon_eq_60
-- name    : RegevRecon.eq_60
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:04:44.452733+00:00
-- url     : https://prove2.me/theorems/d8e7cc53-426d-436b-86a2-1e512744e88c
-- title:
--   (60) — the lifted equality update
-- statement:
--   Fix $\beta\ge0$ and $\ell\ge0$. Let $U\sim\mu$ and, independently, $G=\tilde\eta_1^{(\ell)}*\dots*\tilde\eta_{k-1}^{(\ell)}$ with independent copies. Then, jointly in $x$,
--
--   $$
--   \mathcal L(v^{(\ell)})_x\overset d=\sum_wG(w)\mu_{U-x+w}=\frac{e^{-\beta}+(1-e^{-\beta})\Gamma(U-x)}{c_\beta},
--   $$
--
--   where the second equality holds for every probability vector $G$, with $\Gamma(s)=\sum_{v\in S}G(v-s)$. Up to the constant $1/c_\beta$, this is the likelihood contributed by a constraint in the reconstruction recursion.
--
--   Differences from the source:
--   - reading: (60) under the inductive hypothesis 𝓛(q^(ℓ)) =d η̃^(ℓ) → the law identity with no such hypothesis, for every ℓ; reason: the hypothesis holds for every ℓ by (54), so the unconditional identity is what the induction proves at each depth
--   - encoding: laws of random vectors, =d → finitely supported Law; =d is equality of masses at every whole vector; reason: all these vectors take finitely many values; same instances
-- source:
--   Jordan, Nguyen, Zhou, Regev's Reduction Reaches Reconstruction, STOC 2027 submission (manuscript sha256 9f861d6a…), proof of Theorem 4, (60), p.23

import Mathlib
import Definitions.Def_RegevRecon_qLaw
import Definitions.Def_RegevRecon_etaLaw

namespace RegevRecon

open Filter Topology

/-- **The lifted equality update (60)**. Jordan, Nguyen, Zhou, *Regev's Reduction Reaches Reconstruction*, STOC 2027 submission (manuscript sha256 9f861d6a…), proof of Theorem 4, p.23:
`𝓛(v_t^(ℓ))_x =d Σ_w G_t(w) μ_{U_t−x+w} = (e^{−β} + (1 − e^{−β}) Γ_t(U_t − x))/c_β`, jointly in `x`, with
`G_t` built from `k − 1` independent copies of `η̃^(ℓ)` and `U_t ∼ μ` independent.

**Formalization Note** The first clause is the law identity, with the inductive hypothesis of the proof
discharged by (54). The second clause is the page's closed form, for every probability vector `G`. -/
theorem eq_60 {p : ℕ} [Fact p.Prime] {k D : ℕ} (hk : 3 ≤ k) (hkD : k < D)
    (S : Finset (ZMod p)) (hS : S.Nonempty) (hS' : S ≠ Finset.univ)
    (Λ : PMF (Fin D → (ZMod p)ˣ)) (hΛ : Exchangeable Λ)
    (β : ℝ) (hβ : 0 ≤ β) (ℓ : ℕ) :
    liftLaw (vLaw k D S Λ β ℓ) =
        (branchLaw k S β (etaLaw k D S Λ β ℓ)).map
          (fun b x => ∑ w, b.2 w * channel S β (b.1 - x + w)) ∧
      ∀ (G : Vec p), IsProbVec G → ∀ U x : ZMod p,
        ∑ w, G w * channel S β (U - x + w) =
          (Real.exp (-β) + (1 - Real.exp (-β)) * gammaFn S G (U - x)) / cBeta S β := by sorry

end RegevRecon
