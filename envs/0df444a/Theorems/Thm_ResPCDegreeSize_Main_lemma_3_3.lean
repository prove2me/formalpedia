-- Prove2me | Theorems.Thm_ResPCDegreeSize_Main_lemma_3_3
-- name    : ResPCDegreeSize.Main.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:25:37.534453+00:00
-- url     : https://prove2.me/theorems/5f769389-f79f-4022-9724-b635fba1cc5b
-- title:
--   Lemma 3.3 — kernel descent
-- statement:
--   Let $E=\mathbb F_p(\lambda_1,\dots,\lambda_s)$ and let $M_1,\dots,M_s:U\to W$ be linear maps between finite-dimensional $\mathbb F_p$-spaces. Set
--   $$M(\lambda)=\sum_{i=1}^s\lambda_iM_i,\qquad M(\lambda^p)=\sum_{i=1}^s\lambda_i^pM_i,$$
--   the maps being extended linearly over $E$. If
--   $$\ker_EM(\lambda)\subseteq\ker_EM(\lambda^p),\tag{16}$$
--   then
--   $$\ker_EM(\lambda)=E\otimes_{\mathbb F_p}\bigcap_{i=1}^s\ker M_i.\tag{17}$$
--   In that case, for the stacked map $\mathbf M:U\to W^s$, $\mathbf Mu=(M_1u,\dots,M_su)$,
--   $$\operatorname{rank}_EM(\lambda)=\operatorname{rank}_{\mathbb F_p}\mathbf M,\tag{18}$$
--   and there exists $c\in\mathbb F_p^s$ with
--   $$\operatorname{rank}_{\mathbb F_p}\Bigl(\sum_{i=1}^sc_iM_i\Bigr)\ge\Bigl(1-\frac1p\Bigr)\operatorname{rank}_{\mathbb F_p}\mathbf M.\tag{19}$$
--
--   Without (16) a generic combination can have far smaller rank than the stacked map, so (16) is the condition that makes a single linear combination carry the stacked rank.
--
--   Differences from the source:
--   - encoding: the maps extended linearly over E; rank as a dimension → LinearMap.baseChange on E ⊗ U and Submodule.baseChange for (17); ranks are finrank of ranges; reason: these are the source's tensor extensions, and all spaces are finite dimensional
--   - encoding: E = F_p(λ_1,…,λ_s) → the fraction field of MvPolynomial (Fin s) (ZMod p), with λ_i the images of its variables; reason: the λ_i are then algebraically independent, and any algebraically independent family generates an isomorphic field
--   - encoding: F_p and the stacked map M : U → W^s → ZMod p with [Fact p.Prime] and LinearMap.pi M : U → (Fin s → W); reason: ZMod p is the field with p elements; Fin s → W is W^s
-- source:
--   Pang, A Degree–Size Relation for Resolution over Polynomials, 2026 preprint (STOC 2027 submission #128; SHA-256 d026926040f9df67b9f5a3212fe878d8a10b50dd70b04f14b63b62a9dcb9d32f), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/128.pdf, Lemma 3.3, eqs. (16)–(19), PDF p. 6 (printed p. 5)

import Mathlib
import Definitions.Def_ResPCDegreeSize_Main_PolynomialCalculus
import Definitions.Def_ResPCDegreeSize_Main_RankMaps
open MvPolynomial

namespace ResPCDegreeSize.Main

theorem lemma_3_3 {p s : ℕ} [Fact p.Prime] {U W : Type*}
    [AddCommGroup U] [Module (ZMod p) U] [FiniteDimensional (ZMod p) U]
    [AddCommGroup W] [Module (ZMod p) W] [FiniteDimensional (ZMod p) W]
    (M : Fin s → U →ₗ[ZMod p] W)
    (h16 : LinearMap.ker (mapLam M) ≤ LinearMap.ker (mapLamPow M)) :
    LinearMap.ker (mapLam M) = (⨅ i, LinearMap.ker (M i)).baseChange (FpLam p s) ∧
    Module.finrank (FpLam p s) (LinearMap.range (mapLam M)) =
      Module.finrank (ZMod p) (LinearMap.range (LinearMap.pi M)) ∧
    ∃ c : Fin s → ZMod p,
      (1 - 1 / (p : ℝ)) * (Module.finrank (ZMod p) (LinearMap.range (LinearMap.pi M)) : ℝ) ≤
        (Module.finrank (ZMod p) (LinearMap.range (∑ i, c i • M i)) : ℝ) := by sorry

end ResPCDegreeSize.Main
