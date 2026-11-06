-- Prove2me | Theorems.Thm_SmoothedSimplex_Shadow_shadow_card_ae_le_edgeCount
-- name    : SmoothedSimplex.Shadow.shadow_card_ae_le_edgeCount
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-05T16:34:20.463194+00:00
-- url     : https://prove2.me/theorems/c089f6e3-f2b3-451f-9f46-0a1ca33706fa
-- title:
--   Shadow size is at most the number of edges of the polar polygon $\mathrm{conv}(a_1,\dots,a_n)\cap\mathrm{span}(t,z)$ (a.s.)
-- statement:
--   Let $d\ge3$ and $n\ge d$, let $z,t\in\mathbb R^d$ be linearly independent, $W=\mathrm{span}(t,z)$, and let $a_1,\dots,a_n$ be independent Gaussian vectors $a_i\sim N(\bar a_i,\sigma^2 I_d)$, $\sigma>0$. Then the shadow size $|\mathrm{Shadow}_{t,z}(a_1,\dots,a_n)|$ is an (almost everywhere) measurable random variable, and almost surely
--
--   $$
--   |\mathrm{Shadow}_{t,z}(a_1,\dots,a_n)| \;\le\; \big|\mathrm{edges}\big(\mathrm{conv}(a_1,\dots,a_n)\cap W\big)\big| .
--   $$
--
--   Role: this is the polar-polygon comparison (Borgwardt's duality): the bases optimal for some objective in $W\setminus\{0\}$, i.e. the vertices of the shadow $\pi_W(P)$ of $P=\{x : Ax\le 1\}$, are at most the edges of the polar polygon $\mathrm{conv}(a_1,\dots,a_n)\cap W$. Gaussian rows are non-degenerate with probability one, so the comparison holds almost surely. It transfers any bound on the expected number of edges of the polar polygon to the Spielman–Teng shadow size.
--
--   **Formalization Note**: $|\mathrm{Shadow}_{t,z}|$ is `(shadow t z a).card` (index sets $I$ in $\mathrm{optSimp}_q(a)$ for some nonzero $q\in\mathrm{span}(t,z)$); the edge count is `FriendlyShadow.Gaussian.edgeCount (polygon W a)`; the joint law is `Measure.pi (fun i => gaussian (abar i) σ)`.
-- source:
--   Dadush & Huiberts, A Friendly Smoothed Analysis of the Simplex Method, https://arxiv.org/abs/1711.05667v4, Section 2.5, Lemma 10 and Lemma 11 (|vertices(π_W(P))| ≤ |edges(conv(a_1,…,a_n) ∩ W)| for a non-degenerate shadow; degeneracy has probability 0)

import Mathlib
import Definitions.Def_SmoothedSimplex_Shadow_gaussian
import Definitions.Def_SmoothedSimplex_Shadow_shadow
import Definitions.Def_FriendlyShadow_Gaussian_Model

namespace SmoothedSimplex.Shadow

open MeasureTheory

theorem shadow_card_ae_le_edgeCount {d n : ℕ} (hd : 3 ≤ d) (hn : d ≤ n)
    (z t : EuclideanSpace ℝ (Fin d)) (hzt : LinearIndependent ℝ ![z, t])
    (σ : ℝ) (hσ : 0 < σ) (abar : Fin n → EuclideanSpace ℝ (Fin d)) :
    AEMeasurable (fun a => ((shadow t z a).card : ENNReal))
        (Measure.pi (fun i => gaussian (abar i) σ)) ∧
      ∀ᵐ a ∂(Measure.pi (fun i => gaussian (abar i) σ)),
        (shadow t z a).card ≤
          FriendlyShadow.Gaussian.edgeCount
            (FriendlyShadow.Gaussian.polygon (Submodule.span ℝ {t, z}) a) := by sorry

end SmoothedSimplex.Shadow
