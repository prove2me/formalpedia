-- Prove2me | Theorems.Thm_SuperTableaux_JacobiTrudi_lemma_3_3
-- name    : SuperTableaux.JacobiTrudi.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:29:43.866466+00:00
-- url     : https://prove2.me/theorems/ed0389e2-6802-450c-8877-e788748a2ccb
-- title:
--   Lemma 3.3, p. 12 — the map $\sigma: SST_{[n]}(\lambda)\to SST_{[n]}(\lambda+(1^n))$ is a bijection (shifting content by $(1^n)$)
-- statement:
--   Let $n\ge1$ and $\lambda\in\mathbb Z^n_+$. The map $\sigma$ defined below is a bijection
--   $$\sigma: SST_{[n]}(\lambda)\longrightarrow SST_{[n]}\big(\lambda+(1^n)\big)$$
--   between rational $[n]$-semistandard tableaux of shapes $\lambda$ and $\lambda+(1^n)$, and the content of $\sigma(T)$ is the content of $T$ plus $(1,\dots,1)$, i.e. $\mathrm{wt}_{[n]}(\sigma(T))=\mathrm{wt}_{[n]}(T)+(\epsilon_1+\cdots+\epsilon_n)$.
--
--   The paper's map $\sigma$ replaces the $-1$st column (entries $-b_1<\cdots<-b_t$) by a column $1$ with entries the complement $[n]\setminus\{b_1,\dots,b_t\}$; the weight shift is recorded on p. 23. The lemma reduces rational tableaux to ordinary ones and underlies the shift invariance (4.3) of Kostka numbers.
--
--   **Formalization Note** The map $\sigma$ is the definition `sigmaFill` (p. 12): on a filling of the generalized diagram of $\lambda$ it puts the increasing enumeration of $[n]\setminus\{b_1,\dots,b_t\}$ into the new column $1$ (row $r$, $0$-based, gets $b'_{r+1}$) and moves every other cell one column to the right, the old $-1$st column disappearing. The statement says that there is a bijection $e$ of $SST_{[n]}(\lambda)$ onto $SST_{[n]}(\lambda+(1^n))$ whose underlying filling is `sigmaFill` of the original one, i.e. $\sigma$ maps into $SST_{[n]}(\lambda+(1^n))$ and is bijective; the content clause is the paper's own remark on p. 23 ("recall that $\mathrm{wt}_{[n]}(\sigma(T))=\mathrm{wt}_{[n]}(T)+(\epsilon_1+\cdots+\epsilon_n)$"). Rows are $0$-based; `shift la 1` is $\lambda+(1^n)$.
-- source:
--   Kwon, Rational semistandard tableaux and character formula for the Lie superalgebra ĝl∞|∞, arXiv:math/0605005v1, p. 12, Lemma 3.3 (weight shift recalled on p. 23)

import Mathlib
import Definitions.Def_SuperTableaux_JacobiTrudi_Setting

namespace SuperTableaux.JacobiTrudi
theorem lemma_3_3 (n : ℕ) (hn : 0 < n) (la : GenPartition n) :
    ∃ e : RatTab n la ≃ RatTab n (shift la 1),
      ∀ T, (e T).1 = sigmaFill T.1 ∧ content (e T) = fun k => content T k + 1 := by sorry
end SuperTableaux.JacobiTrudi
