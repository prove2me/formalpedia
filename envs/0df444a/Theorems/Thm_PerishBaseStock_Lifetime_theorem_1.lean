-- Prove2me | Theorems.Thm_PerishBaseStock_Lifetime_theorem_1
-- name    : PerishBaseStock.Lifetime.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T23:11:52.388588+00:00
-- url     : https://prove2.me/theorems/147fc9ef-ace0-42da-b8ff-e767af81e50c
-- title:
--   Theorem 1 — $C_m(\widetilde S_m)-\mathrm{OPT}_m\le\frac{(m-1)\theta}{\lambda m e}e^{\lambda S^{NP}}(\mathbb E[e^{-\lambda D}])^m$
-- statement:
--   Consider the periodic-review perishable lost-sales inventory system with product lifetime $m\ge 1$, zero lead time, FIFO issuance and i.i.d. nonnegative demands distributed as $D$ with $0<\mathbb E[D]<\infty$, with unit holding cost $h>0$, lost-sales penalty $p>0$ and outdating cost $\theta\ge 0$. Let $\mathrm{OPT}_m$ be the optimal long-run average cost over all admissible policies, let $\widetilde S_m$ be any minimizer over $[0,+\infty)$ of
--   $$\widetilde C(S)=h\,\mathbb E[(S-D)^+]+p\,\mathbb E[(D-S)^+]+\frac\theta m\,\mathbb E\Big[\Big(S-\sum_{i=1}^m D_i\Big)^+\Big],$$
--   let $C_m(\widetilde S_m)$ be the long-run average cost of the base-stock policy with level $\widetilde S_m$, and let $S^{NP}=F^{-1}(p/(p+h))$. Then for every $\lambda>0$,
--   $$C_m(\widetilde S_m)-\mathrm{OPT}_m\;\le\;\frac{(m-1)\theta}{\lambda m e}\,e^{\lambda S^{NP}}\cdot\big(\mathbb E[e^{-\lambda D}]\big)^m,$$
--   where $e$ is Euler's number.
--
--   Since $\mathbb E[e^{-\lambda D}]<1$ for every $\lambda>0$, the optimality gap of the heuristic base-stock policy decays to zero exponentially fast in the lifetime $m$. This is the first theoretical performance guarantee for base-stock policies in this system.
--
--   **Formalization Note** The gap is stated as $C_m(\widetilde S_m)\le\mathrm{OPT}_m+B$ in $[0,\infty]$, equivalent to the paper's inequality because $\mathrm{OPT}_m\le C_m(0)<\infty$. The theorem holds for **every** minimizer $\widetilde S_m$, not only the least one. $\mathbb E[e^{-\lambda D}]$ is a Bochner integral of a bounded continuous function, $m-1$ is computed in $\mathbb R$, and $\lambda$ is named `lam` in Lean.
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, SSRN 3724966 (accepted manuscript, 2022), p. 11, Theorem 1, (6)

import Definitions.Def_PerishBaseStock_Lifetime_Model
open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators

namespace PerishBaseStock.Lifetime

theorem theorem_1 (P : CappedBaseStock.DemandLaw) (c : Params) (lam : ℝ) (hlam : 0 < lam)
    (Stilde : ℝ≥0) (hS : IsHeuristicLevel P c Stilde) :
    bsCost P c Stilde ≤ OPT P c + ENNReal.ofReal (((c.m : ℝ) - 1) * c.θ / (lam * c.m * Real.exp 1) *
      Real.exp (lam * (newsvendorNP P c : ℝ)) *
      (∫ x : ℝ≥0, Real.exp (-(lam * (x : ℝ))) ∂P.law) ^ c.m) := by sorry

end PerishBaseStock.Lifetime
