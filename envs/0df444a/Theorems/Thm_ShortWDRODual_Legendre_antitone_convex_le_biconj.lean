-- Prove2me | Theorems.Thm_ShortWDRODual_Legendre_antitone_convex_le_biconj
-- name    : ShortWDRODual.Legendre.antitone_convex_le_biconj
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-04T11:49:49.849535+00:00
-- url     : https://prove2.me/theorems/488a383e-255b-4062-a8e5-24271e60d65e
-- title:
--   Proof of Theorem 1, p. 5 — involution of the Legendre transform for a decreasing convex lsc 𝒢: 𝒢(λ) ≤ sup over ρ > 0 of inf over μ ≥ 0 of μρ + 𝒢(μ) − λρ
-- statement:
--   Let $\mathcal G:\mathbb R\to[-\infty,+\infty]$ be a function which, on $[0,\infty)$, never takes the value $-\infty$, is monotonically decreasing, convex (in the sense $\mathcal G((1-t)a+tb)\le(1-t)\mathcal G(a)+t\,\mathcal G(b)$ for $a,b\ge0$, $t\in[0,1]$, computed in the extended reals), and lower semi-continuous relative to $[0,\infty)$. Then for every $\lambda>0$,
--   $$\mathcal G(\lambda)\;\le\;\sup_{\rho>0}\Big\{\inf_{\mu\ge0}\{\mu\rho+\mathcal G(\mu)\}-\lambda\rho\Big\}.$$
--
--   Writing $\mathcal G$ extended by $+\infty$ on $(-\infty,0)$, the inner infimum is $\mathcal G^*(-\rho)$ up to sign, so the right-hand side is the biconjugate $\mathcal G^{**}(\lambda)$ restricted to affine minorants of negative slope $-\rho$. This is the involution property of the Legendre transform (Fenchel–Moreau: a proper lower semi-continuous convex function equals its biconjugate), specialized to the monotonically decreasing functions of Lemma 2; because $\mathcal G$ is decreasing, affine minorants with slope $\ge0$ can be replaced by ones with slope $-\rho<0$ at an arbitrarily small loss at $\lambda$, so only $\rho>0$ is needed. It is the step of the proof of Theorem 1 (second part) where (D) is converted back into $(-\mathcal L)^*(-\lambda)=\mathcal G(\lambda)$: combined with $\mathcal L(\rho)=\min_{\mu\ge0}\{\mu\rho+\mathcal G(\mu)\}$ it gives $\mathcal G(\lambda)\le\sup_{\rho>0}\{\mathcal L(\rho)-\lambda\rho\}\le(-\mathcal L)^*(-\lambda)$.
--
--   **Formalization note.** Values are in EReal; the hypotheses are exactly the properties that Lemma 2 (p. 13) provides for $\mathcal G$ (lower boundedness by $\mathbb E_{\widehat{\mathbb P}}[f]>-\infty$ gives the `≠ ⊥` hypothesis). Only the inequality $\le$ is stated (the reverse holds trivially by taking $\mu=\lambda$).
-- source:
--   Zhang, Yang & Gao, A Short and General Duality Proof for Wasserstein Distributionally Robust Optimization, arXiv:2205.00362v4, proof of Theorem 1, second part, p. 5 ("by the involution property of Legendre transform", citing Rockafellar, Convex Analysis, Theorem 12.2), applied to 𝒢 with the properties of Lemma 2, p. 13

import Mathlib

namespace ShortWDRODual.Legendre

theorem antitone_convex_le_biconj (G : ℝ → EReal)
    (hbot : ∀ μ : ℝ, 0 ≤ μ → G μ ≠ ⊥)
    (hanti : AntitoneOn G (Set.Ici 0))
    (hconv : ∀ a b t : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ t → t ≤ 1 →
      G ((1 - t) * a + t * b) ≤ ((1 - t : ℝ) : EReal) * G a + ((t : ℝ) : EReal) * G b)
    (hlsc : LowerSemicontinuousOn G (Set.Ici 0))
    (lam : ℝ) (hlam : 0 < lam) :
    G lam ≤ ⨆ (ρ : ℝ) (_ : 0 < ρ),
      ((⨅ (μ : ℝ) (_ : 0 ≤ μ), ((μ * ρ : ℝ) : EReal) + G μ) - ((lam * ρ : ℝ) : EReal)) := by sorry

end ShortWDRODual.Legendre
