-- Prove2me | Theorems.Thm_RobustPrefLearn_MTP_lemma_6
-- name    : RobustPrefLearn.MTP.lemma_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:36:09.471224+00:00
-- url     : https://prove2.me/theorems/aa8c2fe5-5215-4b45-8fb1-d7b18450e238
-- title:
--   Lemma 6, p. 62 — d_S(σ̂_m) = 𝔞_i/𝔟_n if m ∈ S, 0 otherwise
-- statement:
--   Throughout, $K\ge2$ versions and $0<p<1$. Write $d_S(\sigma)=D_S(f^{\mathrm{OA}}_{\sigma_*}\|f^{\mathrm{OA}}_{\sigma})$. For every display set $S$ and every $m\in\{2,\dots,K\}$,
--   $$d_S(\hat\sigma_m)=\begin{cases}\mathfrak a_i/\mathfrak b_n, & m\in S,\\ 0, & m\notin S,\end{cases}\qquad i=\sigma_*(m|S),\ n=|S|.$$
--
--   This closed form turns the max-min problem (5) into the finite linear program (LP-P).
--
--   **Formalization Note** Versions $1,\dots,K$ are `Fin K` (version $m$ is `⟨m-1, _⟩`), and a ranking `σ : Equiv.Perm (Fin K)` sends a version to its rank **0-based**, so `σ X = 0` is the paper's $\sigma(X)=1$. The paper's $m\in\{2,\dots,K\}$ is `1 ≤ m.val`; $i$ is the 1-based restricted rank `relRank 1 S m`. The hypotheses $K\ge2$ ("$K\ge2$ available alternatives", §3) and $0<p<1$ are added: Definition 1 allows $p=0$, but then $\mathcal M_0$ is empty and $\log(1/p)$ is undefined.
-- source:
--   Feng, Caldentey & Ryan, Robust Learning of Consumer Preferences, SSRN 3215614 (https://ssrn.com/abstract=3215614), p. 62, Lemma 6, (49)

import Mathlib
import Definitions.Def_RobustPrefLearn_MTP_OA

open scoped ENNReal

namespace RobustPrefLearn.MTP

/-- Lemma 6, p. 62. For a display set `S` and a version `m ∈ {2, …, K}` (0-based `m.val ≥ 1`),
`d_S(σ̂_m) = D_S(f^OA_{σ*}‖f^OA_{σ̂_m})` equals `𝔞_i/𝔟_n` if `m ∈ S` and `0` otherwise, where
`i = σ*(m|S)` and `n = |S|`. -/
theorem lemma_6 (K : ℕ) (hK : 2 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (m : Fin K)
    (hm : 1 ≤ m.val) (S : DS K) :
    DS_ (oa p (1 : Equiv.Perm (Fin K))) (oa p (sigmaHat m)) S =
      if m ∈ S.1 then aSeq p (relRank (1 : Equiv.Perm (Fin K)) S m) / bSeq p S.1.card else 0 := by sorry

end RobustPrefLearn.MTP
