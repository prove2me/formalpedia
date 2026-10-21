-- Prove2me | Theorems.Thm_PayAsBid_SoftReserve_lemma_4
-- name    : PayAsBid.SoftReserve.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:01:54.642625+00:00
-- url     : https://prove2.me/theorems/2c487f43-26b9-470e-b4c4-9556b845ae33
-- title:
--   Lemma 4, p. A2 — for α = 0, Γ = diag(1/δ), every optimal equitable mechanism is matched by a k-SR with s = b∗_L, r = b∗_H
-- statement:
--   Consider the reduced symmetric model, with $\alpha=0$ and $\Gamma=\mathrm{diag}(1/\delta)$ (that is, $a=0$, $r_c=0$, $r_o=1/\delta$), two-point costs $\Theta_i=\{\theta_L,\theta_H\}$ with $f_i(\theta_L)=f_L$, and the standing assumptions. Let $(q^*,r^*,b^*_L,b^*_H)$ be an optimal solution of Problem (8). Then there is $k\in\{1,\dots,n\}$ such that the $k$-soft-reserve rule $q^{k,b^*_L,b^*_H}$, with soft reserve $s=b^*_L$ and hard reserve $r=b^*_H$, satisfies:
--
--   1. $(q^{k,b^*_L,b^*_H},\,b^*_H,\,b^*_L,\,b^*_H)$ is an optimal solution of Problem (8), so in particular $(b^*_L,b^*_H)$ is an equilibrium pricing strategy under it;
--   2. it yields the same expected consumer surplus:
--   $$ECS(q^{k,b^*_L,b^*_H},b^*_L,b^*_H)=ECS(q^*,b^*_L,b^*_H).$$
--
--   Together with Lemma 2 this gives Proposition 1 for the general symmetric model.
--
--   **Formalization Note.** $k$ ranges over $1,\dots,n$; $k=n$ is the no-competition rule with reserve $b^*_H$ (p. 16). When $b^*_L=b^*_H$ every $k$ gives the no-competition rule, so Definition 5's side condition $s<r$ is not imposed; p. 17 lists both forms ("A k-SR … for $k\le n-1$ and $s<r$", "An NC …").
-- source:
--   Choi, Saban & Weintraub, The Design of Optimal Pay-as-Bid Procurement Mechanisms, SSRN preprint 3785023 (version of 2022-12-08), p. A2 (PDF 35), Lemma 4

import Mathlib
import Definitions.Def_PayAsBid_SoftReserve_Model

namespace PayAsBid.SoftReserve

theorem lemma_4 {n : ℕ} (P : Params n) (hP : P.Standing) (ha : P.a = 0) (hrc : P.rc = 0)
    (q : AssortFn n) (r bL bH : ℝ) (hopt : IsOptimal8 P q r bL bH) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧
      IsOptimal8 P (kSR k bL bH) bH bL bH ∧
      ECS P (kSR k bL bH) bL bH = ECS P q bL bH := by sorry

end PayAsBid.SoftReserve
