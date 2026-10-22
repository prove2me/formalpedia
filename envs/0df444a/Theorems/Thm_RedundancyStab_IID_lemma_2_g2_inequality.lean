-- Prove2me | Theorems.Thm_RedundancyStab_IID_lemma_2_g2_inequality
-- name    : RedundancyStab.IID.lemma_2_g2_inequality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:14:06.895056+00:00
-- url     : https://prove2.me/theorems/9be84602-f499-44b8-b316-2bc0e1469c20
-- title:
--   Proof of Lemma 2, p. 27 — at a most-loaded server s ∈ G₂(n⃗), Σ_{c∈C(s)} Σ_{l∈c} n_c/m_l ≥ d
-- statement:
--   Let $1\le d\le K$ and let $\vec n\in\mathbb R_{\ge0}^{C}$, $\vec n\ne\vec 0$, with $m_l=\sum_{c\in C(l)}n_c$ for each server $l$. If $s\in G_2(\vec n)=\{s\in S: m_s\ge m_l\ \forall l\}$ is a most-loaded server, then
--   $$\sum_{c\in C(s)}\sum_{l\in c}\frac{n_c}{m_l}\;\ge\;\sum_{c\in C(s)}\sum_{l\in c}\frac{n_c}{m_s}=\sum_{c\in C(s)}\frac{d\,n_c}{m_s}=d.$$
--
--   Multiplied by $\mu$, this says that a most-loaded server loses copies at rate at least $\mu d$, which against the copy arrival rate $\lambda d/K$ gives the negative drift of Lemma 2 when $\rho<1$.
--
--   **Formalization Note** `fluidCopies K d n l` is $m_l$; the hypothesis $\vec n\neq\vec0$ is the proof's own "$\vec n\ne\vec 0$" and gives $m_s>0$. Quotients with $m_l=0$ have $n_c=0$ and are $0$ in Lean, as in the paper.
-- source:
--   Anton, Ayesta, Jonckheere & Verloop, On the stability of redundancy models, arXiv:1903.04414v2, p. 27, proof of Lemma 2 (display after the definition of G_2); the same inequality, for the prelimit counts and multiplied by µ, is displayed in §4.1, p. 6

import Mathlib
import Definitions.Def_RedundancyStab_IID_Model

namespace RedundancyStab.IID

theorem lemma_2_g2_inequality (K d : ℕ) (hd : 1 ≤ d) (hdK : d ≤ K) (n : JobType K d → ℝ)
    (hn : ∀ c, 0 ≤ n c) (hne : n ≠ 0) (s : Fin K)
    (hs : ∀ l, fluidCopies K d n l ≤ fluidCopies K d n s) :
    (d : ℝ) ≤ ∑ c ∈ typesAt K d s, ∑ l ∈ c.1, n c / fluidCopies K d n l := by sorry

end RedundancyStab.IID
