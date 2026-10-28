-- Prove2me | Theorems.Thm_PriceRobust_Stability_absolute_norm_near_spectral_radius
-- name    : PriceRobust.Stability.absolute_norm_near_spectral_radius
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:17:28.996414+00:00
-- url     : https://prove2.me/theorems/35f05bb5-7b0c-4208-b36e-a7eb39b09a72
-- title:
--   Proof of Theorem 3(a), p. 16 — for every ε > 0, an absolute norm with ‖Λ(R)‖ ≤ ρ(Λ(R)) + ε
-- statement:
--   Consider the market of §3 with $a\ge 0$ and Assumptions (P), (Z), (IS). For every $\varepsilon>0$ there is an **absolute** vector norm $\|\cdot\|$ on $\mathbb R^{\mathcal N}$ (i.e. $\|x\|=\|\,|x|\,\|$) whose induced matrix norm satisfies
--   $$\|\Lambda(R)\|\le\rho(\Lambda(R))+\varepsilon,$$
--   that is, $\|\Lambda(R)x\|\le(\rho(\Lambda(R))+\varepsilon)\|x\|$ for every $x$.
--
--   The paper attributes this to Horn and Johnson (1985, Lemma 5.6.10), adding that the constructed norm is absolute. That citation does not cover general matrices: Horn and Johnson's construction uses a unitary similarity, which destroys absoluteness, and for $\Lambda=\begin{pmatrix}1&1\\-1&-1\end{pmatrix}$ one has $\rho(\Lambda)=0$ while every absolute norm gives $\|\Lambda\|\ge 1$. The claim as stated here, for the nonnegative matrix $\Lambda(R)$, is true by a different argument (Perron–Frobenius theory).
--
--   **Formalization Note** The norm is a seminorm that vanishes only at $0$. The lower bound $\rho(\Lambda(R))\le\|\Lambda(R)\|$, which holds for every induced norm and is not used in the proof, is omitted. The inequality is stated in $[0,\infty]$ because the spectral radius is valued there.
-- source:
--   Federgruen & Hu, Global robust stability in a general price and assortment competition model, submitted manuscript (TSpace / SSRN 3010503), p. 16 (PDF 17), proof of Theorem 3(a), citing Horn and Johnson (1985), Lemma 5.6.10

import Mathlib
import Definitions.Def_PriceRobust_Stability_Model

open Matrix

namespace PriceRobust.Stability

theorem absolute_norm_near_spectral_radius {ι F : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq F]
    (M : Market ι F) (hM : M.Standing) (ε : ℝ) (hε : 0 < ε) :
    ∃ ν : Seminorm ℝ (ι → ℝ), (∀ x, ν x = 0 → x = 0) ∧
      (∀ x, ν x = ν (fun l => |x l|)) ∧
      ∀ x, ENNReal.ofReal (ν (M.Lam *ᵥ x)) ≤
        (spectralRadius ℂ (M.Lam.map (algebraMap ℝ ℂ)) + ENNReal.ofReal ε) *
          ENNReal.ofReal (ν x) := by sorry

end PriceRobust.Stability
