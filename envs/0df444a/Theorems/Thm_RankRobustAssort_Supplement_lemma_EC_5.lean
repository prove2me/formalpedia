-- Prove2me | Theorems.Thm_RankRobustAssort_Supplement_lemma_EC_5
-- name    : RankRobustAssort.Supplement.lemma_EC_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T03:37:18.104804+00:00
-- url     : https://prove2.me/theorems/4fc4de8c-e9b9-4349-b189-1f92f9d9e35c
-- title:
--   Lemma EC.5 — with the data (EC.15), the system (EC.14) has exactly one solution, the weights (EC.16)
-- statement:
--   Assume, as throughout Appendix E, that the past assortments are reverse revenue-ordered ($\mathcal M=\widetilde{\mathcal S}$, so $M=n$) and $n\ge2$. Let $\bar S\in\widehat{\mathcal S}$ and let the historical data $v$ be the data (EC.15) built from $\bar S$. Then:
--
--   1. the system (EC.14) is nonempty: the weights $\lambda$ of (EC.16),
--   $$
--   \lambda_{i_1\cdots i_n}=\begin{cases}\tfrac1n,& (i_1,\dots,i_n)=(0,\dots,0,j,\dots,j)\ (j\text{ zeros})\text{ for some }j\in\bar S\setminus\{0,n\},\\ \tfrac1n,& (i_1,\dots,i_n)=(n,\dots,n,j,\dots,j)\ (j\text{ copies of }n)\text{ for some }j\in\mathcal N\setminus\bar S,\\ \tfrac1n,&(i_1,\dots,i_n)=(n,\dots,n),\\ 0,&\text{otherwise,}\end{cases}
--   $$
--   solve it; and
--   2. every solution of (EC.14) coincides with these weights on every tuple $(i_1,\dots,i_n)\in\mathcal L$.
--
--   In words, the sales data (EC.15) determine the ranking-based choice model uniquely: one customer type buys $j\in\bar S\setminus\{0,n\}$ or nothing, one prefers $j\notin\bar S$ and then $n$, and one buys $n$ or nothing. This is the core of the proof of Theorem 2.
--
--   **Formalization Note.** Uniqueness is stated for the entries on $\mathcal L$, the variables of (EC.14).
--
--   Differences from the source:
--   - generalization: Appendix E's standing assumption $\eta=0$ → not assumed; reason: the system (EC.14) does not involve $\eta$; with $\eta=0$ it is the paper's statement
--   - generalization: the paper's standing assumption $\mathcal U\ne\emptyset$ (p.8) → not assumed; reason: the statement concerns only the system (EC.14) for the given data, which does not involve $\mathcal U$; part 1 in fact yields a consistent choice model, so instances with $\mathcal U=\emptyset$ do not occur
-- source:
--   Sturt, The value of robust assortment optimization under ranking-based choice models, arXiv:2112.05010v4, Lemma EC.5 and (EC.14)–(EC.16), p.ec27; Appendix E.1, p.ec26

import Mathlib
import Definitions.Def_RankRobustAssort_SHat
import Definitions.Def_RankRobustAssort_Supplement_revPast
import Definitions.Def_RankRobustAssort_Supplement_vEC15
import Definitions.Def_RankRobustAssort_Supplement_lamEC16
import Definitions.Def_RankRobustAssort_Supplement_systemEC14

namespace RankRobustAssort.Supplement

/-- **Lemma EC.5.** Suppose `ℳ = S̃`, `n ≥ 2`, `S̄ ∈ Ŝ`, and the historical data is (EC.15).
Then the system (EC.14) is nonempty and has a unique solution `λ`, which satisfies (EC.16) for
each `(i₁,…,i_n) ∈ ℒ`.

Sturt, arXiv:2112.05010v4, Lemma EC.5, p.ec27; standing assumptions of Appendix E (E.1, p.ec26);
(EC.14), (EC.15), (EC.16), p.ec27.

Formalization Note: `ℳ = S̃` is `P.S = revPast n`, the data (EC.15) is `P.v = vEC15 n S̄`. The
conclusion has two parts: the vector (EC.16) (`lamEC16`) solves (EC.14) (so the system is
nonempty), and every solution agrees with it on `ℒ` (uniqueness of `λ = (λ_t)_{t∈ℒ}`; entries off
`ℒ` are not variables of (EC.14)). The Appendix E assumption `η = 0` is not needed: the system
(EC.14) does not involve `η`. The revenues and the norm of `P` are arbitrary. -/
theorem lemma_EC_5 {n : ℕ} (hn : 2 ≤ n) (P : Problem n n) (hS : P.S = revPast n)
    (Sbar : Finset (Fin (n + 1))) (hSbar : Sbar ∈ SHat P) (hv : P.v = vEC15 n Sbar) :
    systemEC14 P (lamEC16 n Sbar) ∧
      ∀ μ : (Fin n → Fin (n + 1)) → ℝ, systemEC14 P μ →
        ∀ t, InL P t → μ t = lamEC16 n Sbar t := by sorry

end RankRobustAssort.Supplement
