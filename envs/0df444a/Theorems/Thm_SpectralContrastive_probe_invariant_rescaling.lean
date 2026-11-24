-- Prove2me | Theorems.Thm_SpectralContrastive_probe_invariant_rescaling
-- name    : SpectralContrastive.probe_invariant_rescaling
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-23T18:35:08.235141+00:00
-- url     : https://prove2.me/theorems/d2e04890-1238-4299-b3e3-172121aac90c
-- title:
--   Lemma 3.1: row scaling and invertible right factors preserve the linear probe
-- statement:
--   Let $F\in\mathbb R^{N\times k}$ be an embedding matrix whose rows $u_x$ are the representations, let $D=\mathrm{diag}(s)$ with $s_x>0$ for all $x$, and let $Q\in\mathbb R^{k\times k}$ be invertible. Put $\widetilde F=DFQ$, with rows $\tilde u_x$. Then for every linear classifier $B\in\mathbb R^{k\times r}$ the classifier $\widetilde B=Q^{-1}B$ on $\widetilde F$ makes the same predictions as $B$ on $F$:
--
--   $$\arg\max_i(\tilde u_x^\top\widetilde B)_i=\arg\max_i(u_x^\top B)_i\quad\text{for every }x\in\mathcal X.$$
--
--   Consequently the linear probe errors agree: $\mathcal E(F)=\mathcal E(\widetilde F)$, where $\mathcal E(F)$ is the linear probe error with the rows of $F$ as embeddings.
--
--   This is why the spectral embedding only needs to be learned up to row scaling and a right invertible transformation.
--
--   **Formalization Note** "Same prediction" is stated as equality of the argmax sets, which covers every tie-breaking rule.
-- source:
--   HaoChen, Wei, Gaidon and Ma, Provable Guarantees for Self-Supervised Deep Learning with Spectral Contrastive Loss, arXiv:2106.04156v7 (NeurIPS 2021), Section 3.2, Lemma 3.1, eq. (5), p. 8

import Mathlib
import Definitions.Def_SpectralContrastive_Basic

open Matrix

namespace SpectralContrastive

theorem probe_invariant_rescaling {Xbar X : Type*} [Fintype Xbar] [Fintype X] [DecidableEq X]
    {k r : ℕ} (P : Xbar → ℝ) (A : Xbar → X → ℝ) (y : Xbar → Fin r)
    (F : Matrix X (Fin k) ℝ) (s : X → ℝ) (hs : ∀ x, 0 < s x)
    (Q : Matrix (Fin k) (Fin k) ℝ) (hQ : IsUnit Q.det) :
    (∀ (B : Matrix (Fin k) (Fin r) ℝ) (x : X) (i : Fin r),
      (∀ j, vecMul ((diagonal s * F * Q) x) (Q⁻¹ * B) j ≤
          vecMul ((diagonal s * F * Q) x) (Q⁻¹ * B) i) ↔
        (∀ j, vecMul (F x) B j ≤ vecMul (F x) B i)) ∧
    linearProbeError P A y (diagonal s * F * Q) = linearProbeError P A y F := by sorry

end SpectralContrastive
