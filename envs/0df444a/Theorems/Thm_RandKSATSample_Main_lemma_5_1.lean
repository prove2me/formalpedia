-- Prove2me | Theorems.Thm_RandKSATSample_Main_lemma_5_1
-- name    : RandKSATSample.Main.lemma_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:00:49.908182+00:00
-- url     : https://prove2.me/theorems/b6918e18-8506-43b5-b931-2099a65bbc6b
-- title:
--   Lemma 5.1 — inclusion–exclusion over connected sets: µ_{F⁻}1_{B_a} = Σ_{S∈CS_F(a)} (−1)^{|S|−1} w_S η_S, and O − E = µ_{F⁻}(B_a)
-- statement:
--   For every $F\subseteq\mathcal F=\mathcal C^{\mathrm{good}}$ and $a\in F$, with $F^-=F\setminus\{a\}$, $Z_{F^-}>0$, and $w_S$, $\eta_S$ as in (5.1),
--   $$\mu_{F^-}\mathbf 1_{B_a}=\sum_{S\in\mathsf{CS}_F(a)}(-1)^{|S|-1}w_S\,\eta_S,$$
--   i.e. $\mu_{F^-}(A\cap B_a)=\sum_S(-1)^{|S|-1}w_S\eta_S(A)$ for every event $A$ on the good variables. Moreover, with $O=\sum_{S\in\mathsf{CS}_F(a):|S|\text{ odd}}w_S$ and $E=\sum_{S\in\mathsf{CS}_F(a):|S|\text{ even}}w_S$, $O-E=\mu_{F^-}(B_a)$. The identity is the basis of the residual sampler's local marginal coins.
--
--   Differences from the source:
--   - generalization: Φ a nice formula (§5 standing assumption, p. 37), with Z_F > 0 assumed for the measures used → any formula Φ, with the hypothesis Z_{F⁻} > 0; reason: the identity is inclusion–exclusion plus independence of E_S and Good(F_S) under ν_good, which hold for every formula; a nice formula has Z_{F⁻} > 0 by Lemma 3.9, so the statement specializes to the source
--   - encoding: µ_{F⁻}1_{B_a} as a measure → ∀ events A : PartAssign → Prop, µ_{F⁻}(A ∧ B_a) = …; reason: two measures on a finite set agree iff they agree on every event
-- source:
--   He, Li, Yang, Fast Almost-Uniform Sampling of Random k-SAT Solutions, arXiv:2610.10474 (version not printed; file sha256 563a4d84…), p. 38, Lemma 5.1

import Mathlib
import Definitions.Def_RandKSATSample_Main_Formula
import Definitions.Def_RandKSATSample_Main_Structure
import Definitions.Def_RandKSATSample_Main_ResidualIE

set_option autoImplicit false

open Classical

namespace RandKSATSample.Main

/-- Lemma 5.1 (inclusion–exclusion over connected sets): for `F ⊆ 𝓕 = C_good`, `a ∈ F` and
`F⁻ = F ∖ {a}` with `Z_{F⁻} > 0`, every event `A` satisfies
`µ_{F⁻}(A ∩ B_a) = Σ_{S ∈ CS_F(a)} (−1)^{|S|−1} w_S η_S(A)`, and
`O − E = µ_{F⁻}(B_a)` with `O`, `E` the sums of `w_S` over odd and even `|S|`. -/
theorem lemma_5_1 {n m k : ℕ} (Φ : Formula n m k) (F : Finset (Fin m)) (hF : F ⊆ Cgood Φ)
    (a : Fin m) (ha : a ∈ F) (hZ : 0 < Zf Φ (F.erase a)) :
    (∀ A : PartAssign n (Vgood Φ) → Prop,
      muF Φ (F.erase a) (fun τ => A τ ∧ Viol Φ a τ) =
        ∑ S ∈ CSin Φ F a, (-1 : ℝ) ^ (S.card - 1) * wS Φ F a S * etaS Φ F S A) ∧
    (∑ S ∈ (CSin Φ F a).filter (fun S => Odd S.card), wS Φ F a S) -
        (∑ S ∈ (CSin Φ F a).filter (fun S => Even S.card), wS Φ F a S) =
      muF Φ (F.erase a) (Viol Φ a) := by sorry

end RandKSATSample.Main
