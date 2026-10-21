-- Prove2me | Theorems.Thm_ShortTermDisclosure_Equilibrium_lemma_1
-- name    : ShortTermDisclosure.Equilibrium.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:43:00.33282+00:00
-- url     : https://prove2.me/theorems/af1da851-47ff-48b3-8ca3-5b495d14f716
-- title:
--   Lemma 1 — shareholder intervention threshold
-- statement:
--   Let $x=E[v\mid d]$ be the belief after disclosure decision $d$, with $\bar\mu/2<x<\bar\mu$, and let $\eta\in[0,1]$. A threshold strategy is a weak shareholder best response exactly when
--
--   $$\mu^*(d)=(1+\lambda)x-\lambda\bar\mu,\qquad\lambda=\frac{\eta}{2-\eta}.$$
--
--   Types below this threshold abstain and types at or above it intervene. This is the intervention rule used by the equilibrium. **Formalization Note** Best response is defined from utility, so the formula remains a theorem.
-- source:
--   Jia & Menon, Shareholder short-termism, corporate control and voluntary disclosure, authors' manuscript (SSRN 4029096, Minerva Access copy), p. 11 (PDF 14), Lemma 1 and (5)

import Mathlib
import Definitions.Def_ShortTermDisclosure_Equilibrium_Model

namespace ShortTermDisclosure.Equilibrium

theorem lemma_1 (η muhi x t : ℝ)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hm : 0 < muhi)
    (hx0 : muhi / 2 < x) (hx1 : x < muhi) :
    IsSHBestResponse η muhi x t ↔
      t = (1 + lam η) * x - lam η * muhi := by sorry

end ShortTermDisclosure.Equilibrium
