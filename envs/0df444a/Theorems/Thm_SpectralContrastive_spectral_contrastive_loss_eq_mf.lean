-- Prove2me | Theorems.Thm_SpectralContrastive_spectral_contrastive_loss_eq_mf
-- name    : SpectralContrastive.spectral_contrastive_loss_eq_mf
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-23T18:36:01.951371+00:00
-- url     : https://prove2.me/theorems/2d8c7bbc-cb1a-47dd-8a5e-c7bf66433041
-- title:
--   Lemma 3.2: spectral contrastive loss
-- statement:
--   Consider the finite data model with augmentation graph weights $w_{xx'}$ and degrees $w_x>0$. For a feature map $f:\mathcal X\to\mathbb R^k$, let $F\in\mathbb R^{N\times k}$ have rows $u_x=w_x^{1/2}f(x)$. Then there is a constant $c$, depending only on the graph and not on $f$, such that for every $f$
--
--   $$\mathcal L_{\mathrm{mf}}(F)=\|\overline A-FF^\top\|_F^2=\mathcal L(f)+c,\qquad \mathcal L(f)=-2\,\mathbb E_{x,x^+}[f(x)^\top f(x^+)]+\mathbb E_{x,x^-}[(f(x)^\top f(x^-))^2].$$
--
--   So minimizing the spectral contrastive loss is the same as computing a rank-$k$ factorization of the normalized adjacency matrix.
-- source:
--   HaoChen, Wei, Gaidon and Ma, Provable Guarantees for Self-Supervised Deep Learning with Spectral Contrastive Loss, arXiv:2106.04156v7 (NeurIPS 2021), Section 3.2, Lemma 3.2, eqs. (4), (6), (7), p. 9; also eqs. (20)-(21), p. 30

import Mathlib
import Definitions.Def_SpectralContrastive_Basic

open Matrix

namespace SpectralContrastive

theorem spectral_contrastive_loss_eq_mf {Xbar X : Type*} [Fintype Xbar] [Fintype X]
    [DecidableEq X] {k : ℕ} (P : Xbar → ℝ) (A : Xbar → X → ℝ) (hM : IsAugModel P A) :
    ∃ c : ℝ, ∀ f : X → Fin k → ℝ,
      mfLoss (augWeight P A) (fun x i => Real.sqrt (degree (augWeight P A) x) * f x i) =
        scLoss P A f + c := by sorry

end SpectralContrastive
