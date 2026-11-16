-- Prove2me | Theorems.Thm_StabPauli1264_Grouped_Supplement_independent_set_mixtures
-- name    : StabPauli1264.Grouped.Supplement.independent_set_mixtures
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T06:53:29.029563+00:00
-- url     : https://prove2.me/theorems/6a04497b-9b85-4959-bf3a-5a29d5bc34ef
-- title:
--   Lemma 3.2 — Independent-set mixtures
-- statement:
--   Let $H$ be a graph on $[m]$, $m\ge1$, and $D$ a distribution on graph independent sets of $H$ with $\Pr_{T\sim D}[v\in T]=\beta$ for every vertex $v$. On the window $M_H$ the state
--
--   $$\rho_D=\mathbb E_{T\sim D}\,2^{-m}\prod_{v\in T}(I+P_v)$$
--
--   is a stabilizer mixture with $b_v=\operatorname{tr}(\rho_DP_v)=\beta$ for all $v$, and under the uniform distribution $p$ every $f\in F_{M_H}$ satisfies
--
--   $$R(f)-R^*=\frac{\beta}{2m}\Big(\alpha(H)-\sum_vf(v)\Big).$$
--
--   These are the physical, classically samplable hard targets of the hardness reductions.
--
--   Differences from the source:
--   - encoding: a distribution D on independent sets → a finite law on subsets of Fin m with real masses vanishing off independent sets; reason: same objects
--   - encoding: a graph on [m] → m ≥ 1; reason: windows are nonempty (standing assumption)
-- source:
--   Yingjian Liu, Xiaoyi Yang, Zhaohui Yang, STOC 2027 submission #1264 (October 2026), Lemma 3.2 and Eqs. (10)–(11), p. 10; proof p. 28; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1264.pdf

import Definitions.Def_StabPauli1264_Grouped_Supplement_Structure
set_option autoImplicit false

namespace StabPauli1264.Grouped.Supplement

open QAlgorithms.Stabilizer StabPauli1264.Grouped
open scoped BigOperators Classical

/-- Lemma 3.2 (Independent-set mixtures), p. 10: for a law `D` on independent sets of `H` with all
marginals `β`, `ρ_D` (Eq. (10)) is a stabilizer mixture with `b_v = β`, and under uniform `p`
every `f ∈ F_{M_H}` has excess risk `(β/2m)(α(H) − ∑_v f(v))` (Eq. (11)). -/
theorem independent_set_mixtures {m : ℕ} (H : SimpleGraph (Fin m)) (hm : 0 < m)
    (D : OAI.ThorpCompatibility.Law (Finset (Fin m))) (β : ℝ) (hD : IsUniformIndepLaw H D β) :
    IsStabilizerMixture (setMixture (graphWindow H hm) D) ∧
    (∀ v, bias (graphWindow H hm) (setMixture (graphWindow H hm) D) v = β) ∧
    ∀ f ∈ responses (graphWindow H hm),
      excess (graphWindow H hm) (uniformLaw m hm) (setMixture (graphWindow H hm) D) f =
        β / (2 * m) * (indepWeight H (fun _ => 1) - ∑ v, f v) := by sorry

end StabPauli1264.Grouped.Supplement
