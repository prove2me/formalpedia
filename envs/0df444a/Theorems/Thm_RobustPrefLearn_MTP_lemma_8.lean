-- Prove2me | Theorems.Thm_RobustPrefLearn_MTP_lemma_8
-- name    : RobustPrefLearn.MTP.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:36:25.04832+00:00
-- url     : https://prove2.me/theorems/94b7e690-b453-4a7f-ab1f-a3c1788d31ac
-- title:
--   Lemma 8, p. 63 — (µ*, l*) is feasible in (LP-D)
-- statement:
--   Throughout, $K\ge2$ versions and $0<p<1$. The pair $(\mu^*,l^*)$ of (50)–(51), $l^*=1/(\mu_2+\dots+\mu_K)$, is feasible in
--   $$\min_{\mu,l}\ l\quad\text{s.t.}\quad \sum_{\bar\sigma\in\overline\Sigma(\sigma_*)}d_S(\bar\sigma)\mu(\bar\sigma)\le l\ \ \forall S\in\mathcal S,\qquad \sum_{\bar\sigma\in\overline\Sigma(\sigma_*)}\mu(\bar\sigma)=1,\ \mu\ge0. \tag{LP-D}$$
--
--   This is the dual certificate for Theorem 4.
--
--   **Formalization Note** Versions $1,\dots,K$ are `Fin K` (version $m$ is `⟨m-1, _⟩`), and a ranking `σ : Equiv.Perm (Fin K)` sends a version to its rank **0-based**, so `σ X = 0` is the paper's $\sigma(X)=1$. $\mu^*$ is a function on all rankings, supported on $\{\hat\sigma_m: m\ge2\}\subseteq\overline\Sigma(\sigma_*)$; nonnegativity is stated for every ranking. The hypotheses $K\ge2$ ("$K\ge2$ available alternatives", §3) and $0<p<1$ are added: Definition 1 allows $p=0$, but then $\mathcal M_0$ is empty and $\log(1/p)$ is undefined.
-- source:
--   Feng, Caldentey & Ryan, Robust Learning of Consumer Preferences, SSRN 3215614 (https://ssrn.com/abstract=3215614), p. 62, (LP-D); p. 63, (50), (51), Lemma 8

import Mathlib
import Definitions.Def_RobustPrefLearn_MTP_OA

open scoped ENNReal

namespace RobustPrefLearn.MTP

/-- Lemma 8, p. 63. `(µ*, l*)` is feasible in (LP-D), where `l* = 1/(µ_2 + ⋯ + µ_K)`: `µ* ≥ 0`,
`∑_{σ̄ ∈ Σ̄(σ*)} µ*(σ̄) = 1`, and `∑_{σ̄ ∈ Σ̄(σ*)} d_S(σ̄) µ*(σ̄) ≤ l*` for every display set `S`. -/
theorem lemma_8 (K : ℕ) (hK : 2 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    (∀ σbar : Equiv.Perm (Fin K), 0 ≤ muStar K p σbar) ∧
    ∑ σbar ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin K) => NotTopOne σ), muStar K p σbar = 1 ∧
    ∀ S : DS K,
      ∑ σbar ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin K) => NotTopOne σ),
        DS_ (oa p (1 : Equiv.Perm (Fin K))) (oa p σbar) S * muStar K p σbar ≤ lStar K p := by sorry

end RobustPrefLearn.MTP
