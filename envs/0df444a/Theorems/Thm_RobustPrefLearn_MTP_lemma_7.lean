-- Prove2me | Theorems.Thm_RobustPrefLearn_MTP_lemma_7
-- name    : RobustPrefLearn.MTP.lemma_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:36:03.322825+00:00
-- url     : https://prove2.me/theorems/6a6b7d52-2f50-4d06-a414-9c9bada205ff
-- title:
--   Lemma 7, p. 63 — (λ^OA_*, u*) is feasible in (LP-P)
-- statement:
--   Throughout, $K\ge2$ versions and $0<p<1$. With $d_S(\bar\sigma)=D_S(f^{\mathrm{OA}}_{\sigma_*}\|f^{\mathrm{OA}}_{\bar\sigma})$, the pair $(\lambda^{\mathrm{OA}}_*,u^*)$, $u^*=1/(\lambda^*_2+\dots+\lambda^*_K)$, is feasible in
--   $$\max_{\lambda,u}\ u\quad\text{s.t.}\quad \sum_{S\in\mathcal S}d_S(\bar\sigma)\lambda(S)\ge u\ \ \forall\bar\sigma\in\overline\Sigma(\sigma_*),\qquad \sum_S\lambda(S)=1,\ \lambda\ge0, \tag{LP-P}$$
--   where $\overline\Sigma(\sigma_*)$ is the set of rankings whose top-ranked version is not version $1$.
--
--   Together with Lemmas 8 and 9 this certifies the optimality of $\lambda^{\mathrm{OA}}_*$ by weak duality.
--
--   **Formalization Note** Versions $1,\dots,K$ are `Fin K` (version $m$ is `⟨m-1, _⟩`), and a ranking `σ : Equiv.Perm (Fin K)` sends a version to its rank **0-based**, so `σ X = 0` is the paper's $\sigma(X)=1$. Membership in $\overline\Sigma(\sigma_*)$ is `NotTopOne`. The hypotheses $K\ge2$ ("$K\ge2$ available alternatives", §3) and $0<p<1$ are added: Definition 1 allows $p=0$, but then $\mathcal M_0$ is empty and $\log(1/p)$ is undefined.
-- source:
--   Feng, Caldentey & Ryan, Robust Learning of Consumer Preferences, SSRN 3215614 (https://ssrn.com/abstract=3215614), p. 62, (LP-P); p. 63, Lemma 7

import Mathlib
import Definitions.Def_RobustPrefLearn_MTP_OA

open scoped ENNReal

namespace RobustPrefLearn.MTP

/-- Lemma 7, p. 63. `(λ^OA_*, u*)` is feasible in (LP-P), where `u* = 1/(λ*_2 + ⋯ + λ*_K)`:
`λ^OA_* ∈ Δ(𝒮)` and `∑_S d_S(σ̄) λ^OA_*(S) ≥ u*` for every ranking `σ̄ ∈ Σ̄(σ*)` whose top-ranked
version is not version 1, with `d_S(σ̄) = D_S(f^OA_{σ*}‖f^OA_{σ̄})`. -/
theorem lemma_7 (K : ℕ) (hK : 2 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    lamOA K p ∈ simplex K ∧
    ∀ σbar : Equiv.Perm (Fin K), NotTopOne σbar →
      uStar K p ≤ ∑ S, DS_ (oa p (1 : Equiv.Perm (Fin K))) (oa p σbar) S * lamOA K p S := by sorry

end RobustPrefLearn.MTP
