-- Prove2me | Theorems.Thm_TiltedCvx_lemma_1
-- name    : TiltedCvx.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:40:19.907828+00:00
-- url     : https://prove2.me/theorems/2defe2db-184a-4350-8c56-5bb9bda37a3c
-- title:
--   Lemma 1 — properties of the tilts $\psi_\gamma$ and $\bar\psi_\gamma$
-- statement:
--   Let $a,b\in\mathbb R$ and $\gamma,\gamma'\in[0,1]$. Then:
--
--   1. If $\gamma>0$, both $\psi_\gamma$ and $\bar\psi_\gamma$ are continuous, monotone increasing, bijective and positively homogeneous.
--   2. Whenever $\psi_\gamma(a)$ and $\bar\psi_\gamma(a)$ are defined, $\psi_\gamma(a)\le a\le\bar\psi_\gamma(a)$.
--   3. $\bar\psi_\gamma(a)=-\psi_\gamma(-a)$ whenever both sides are defined.
--   4. $\psi_\gamma(\psi_{\gamma'}(a))=\psi_{\gamma\gamma'}(a)$ whenever both sides are defined.
--   5. If $\gamma>0$, then $\psi_\gamma(a)+\psi_\gamma(b)\le\psi_\gamma(a+b)$ and $\bar\psi_\gamma(a)+\bar\psi_\gamma(b)\ge\bar\psi_\gamma(a+b)$.
--   6. If $\gamma>0$, then $\bar\psi_\gamma(\psi_\gamma(a))=\psi_\gamma(\bar\psi_\gamma(a))=a$.
--   7. If $\gamma'<\gamma$ and $\psi_{\gamma'}(a)$ is defined, then $\psi_{\gamma'}(a)\le\psi_\gamma(a)$.
--
--   These rules are the calculus behind every comparison of the tilted classes: item 4 turns two tilts into one with the product parameter (the source of the square in Theorem 14), and item 7 makes each class shrink as $\gamma$ grows.
--
--   **Formalization Note** The tilts are maps $\overline{\mathbb R}\to\overline{\mathbb R}$; item 1 is stated for these maps, with positive homogeneity $\psi_\gamma(cz)=c\,\psi_\gamma(z)$ for real $c>0$. Each "defined" is a `TiltDefined` hypothesis; in item 4 each of the three tilts $\psi_{\gamma'}(a)$, $\psi_\gamma(\psi_{\gamma'}(a))$ and $\psi_{\gamma\gamma'}(a)$ gets one.
--
--   Differences from the source:
--   - reading: item 1: ψγ, ψ̄γ continuous, monotone increasing, bijective, positively homogeneous → the same properties of the maps EReal → EReal, homogeneity for real factors c > 0; reason: p.12 defines the tilts over the extended reals; they map ℝ onto ℝ and ±∞ to ±∞, so the statement contains the real one
--   - encoding: whenever … defined → explicit TiltDefined hypotheses (γ ≠ 0 or argument ≠ 0); reason: the only undefined case is γ = 0 at 0; same instances
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Lemma 1, pp.12–13

import Mathlib
import Definitions.Def_TiltedCvx_psi
import Definitions.Def_TiltedCvx_psiBar
import Definitions.Def_TiltedCvx_TiltDefined

namespace TiltedCvx

/-- **Lemma 1 (properties of the tilts).** Pedramfar–Khanna–Quinn–Aggarwal, *Tilted Convexity and
an Exact Offline–Online Separation*, arXiv:2611.03472, Lemma 1, pp.12–13. Let `a, b ∈ ℝ` and
`γ, γ′ ∈ [0, 1]`.
1. If `γ > 0`, then `ψγ` and `ψ̄γ` are continuous, monotone increasing, bijective and positively
   homogeneous.
2. Whenever `ψγ(a)` and `ψ̄γ(a)` are defined, `ψγ(a) ≤ a ≤ ψ̄γ(a)`.
3. `ψ̄γ(a) = −ψγ(−a)` whenever both sides are defined.
4. `ψγ(ψγ′(a)) = ψγγ′(a)` whenever both sides are defined.
5. If `γ > 0`, then `ψγ(a) + ψγ(b) ≤ ψγ(a + b)` and `ψ̄γ(a) + ψ̄γ(b) ≥ ψ̄γ(a + b)`.
6. If `γ > 0`, then `ψ̄γ(ψγ(a)) = ψγ(ψ̄γ(a)) = a`.
7. If `γ′ < γ` and `ψγ′(a) is defined, then `ψγ′(a) ≤ ψγ(a)`.

**Formalization Note** The tilts are functions `EReal → EReal`, as the paper defines them "over
extended real numbers"; item 1 is stated for these functions (positive homogeneity for real
factors `c > 0`). Each "defined" is a `TiltDefined` hypothesis; in item 4 the three tilts
`ψγ′(a)`, `ψγ(ψγ′(a))` and `ψγγ′(a)` each get one. -/
theorem lemma_1 (γ γ' : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1) (hγ' : γ' ∈ Set.Icc (0 : ℝ) 1)
    (a b : ℝ) :
    (0 < γ →
      (Continuous (psi γ) ∧ Monotone (psi γ) ∧ Function.Bijective (psi γ) ∧
        ∀ c : ℝ, 0 < c → ∀ z : EReal, psi γ ((c : EReal) * z) = (c : EReal) * psi γ z) ∧
      (Continuous (psiBar γ) ∧ Monotone (psiBar γ) ∧ Function.Bijective (psiBar γ) ∧
        ∀ c : ℝ, 0 < c → ∀ z : EReal, psiBar γ ((c : EReal) * z) = (c : EReal) * psiBar γ z)) ∧
    (TiltDefined γ (a : EReal) →
      psi γ (a : EReal) ≤ (a : EReal) ∧ (a : EReal) ≤ psiBar γ (a : EReal)) ∧
    (TiltDefined γ (a : EReal) → TiltDefined γ (-(a : EReal)) →
      psiBar γ (a : EReal) = -psi γ (-(a : EReal))) ∧
    (TiltDefined γ' (a : EReal) → TiltDefined γ (psi γ' (a : EReal)) →
      TiltDefined (γ * γ') (a : EReal) →
      psi γ (psi γ' (a : EReal)) = psi (γ * γ') (a : EReal)) ∧
    (0 < γ →
      psi γ (a : EReal) + psi γ (b : EReal) ≤ psi γ ((a + b : ℝ) : EReal) ∧
      psiBar γ ((a + b : ℝ) : EReal) ≤ psiBar γ (a : EReal) + psiBar γ (b : EReal)) ∧
    (0 < γ →
      psiBar γ (psi γ (a : EReal)) = (a : EReal) ∧ psi γ (psiBar γ (a : EReal)) = (a : EReal)) ∧
    (γ' < γ → TiltDefined γ' (a : EReal) → psi γ' (a : EReal) ≤ psi γ (a : EReal)) := by sorry

end TiltedCvx
