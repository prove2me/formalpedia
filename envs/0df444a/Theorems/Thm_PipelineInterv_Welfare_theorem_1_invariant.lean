-- Prove2me | Theorems.Thm_PipelineInterv_Welfare_theorem_1_invariant
-- name    : PipelineInterv.Welfare.theorem_1_invariant
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:23:08.714448+00:00
-- url     : https://prove2.me/theorems/fc04268b-3b6e-49cb-95f7-35c283ef0a53
-- title:
--   Proof of Theorem 1, p. 12 — induction invariant R⊤M(B≥t, Dt)Dt ≥ OPT^ε − 2(k−t)ε‖R‖∞
-- statement:
--   Fix an instance with $k$ layers satisfying the standing assumptions of §2, a budget $B\ge0$, $\varepsilon>0$, an $\varepsilon$-net $S$ of $\mathcal D$ in $\ell_1$, and any run $M(\cdot,\cdot)$ of Algorithm 1 with these parameters. Let $n_1,\dots,n_{k-1}\in\mathbb N$ and matrices $M^\varepsilon_1,\dots,M^\varepsilon_{k-1}$ satisfy $\sum_t n_t\varepsilon\le B$ and, for every $t$, be feasible for Program (7) with budget $B^\varepsilon_t=n_t\varepsilon$. Write $B^\varepsilon_{\ge t}=B^\varepsilon_t+\dots+B^\varepsilon_{k-1}$ and $D^\varepsilon_t=M^\varepsilon_{t-1}\cdots M^\varepsilon_1D_1$.
--
--   Then for every layer $t\in\{1,\dots,k-1\}$, every grid budget $B_{\ge t}\le B$ with $B_{\ge t}\ge B^\varepsilon_{\ge t}$, and every distribution $D_t$ considered by the algorithm at layer $t$ (an element of $S$, or $D_1$ when $t=1$) with $\|D_t-D^\varepsilon_t\|_1\le\varepsilon$,
--   $$R^\top M(B_{\ge t},D_t)\,D_t\ \ge\ W(M^\varepsilon_1,\dots,M^\varepsilon_{k-1})-2(k-t)\,\varepsilon\,\|R\|_\infty .$$
--
--   At $t=1$, $B_{\ge 1}=B^\varepsilon$ and $D_1$ itself, this says that the value found by the dynamic program is within $2(k-1)\varepsilon\|R\|_\infty$ of the welfare of any budget-discretized solution.
--
--   **Formalization Note.** The paper's $OPT^\varepsilon$ is any value with $R^\top M^\varepsilon_{k-1}\cdots M^\varepsilon_1D_1\ge OPT^\varepsilon$; the statement uses the welfare $W(M^\varepsilon)$ itself, which is what the proof uses. Transitions are 0-based: Lean index $t$ is the paper's layer $t+1$, so with $K=k-1$ the Lean factor $2(K-t)=2(k-(t+1))$ is the paper's $2(k-t_{\text{paper}})$ at layer $t_{\text{paper}}=t+1$. The table entry $M(B_{\ge t},D_t)$ is the suffix product of the stored tuple from index $t$.
-- source:
--   Arunachaleswaran, Kannan, Roth, Ziani, Pipeline Interventions, arXiv:2002.06592v2, p. 12, proof of Theorem 1, induction claim 'To prove the result, we will show by induction that …'

import Mathlib
import Definitions.Def_PipelineInterv_Welfare_Model

namespace PipelineInterv.Welfare
open Matrix

theorem theorem_1_invariant {w K : ℕ} (I : Instance w K) (hI : I.Standing) (B ε : ℝ)
    (hB : 0 ≤ B) (hε : 0 < ε) (S : Finset (Fin w → ℝ)) (hS : IsEpsNet ε S) (tab : Table w K)
    (hrun : IsAlg1Run I B ε S tab) (n : Fin K → ℕ) (Meps : Fin K → Matrix (Fin w) (Fin w) ℝ)
    (hn : ∑ s, (n s : ℝ) * ε ≤ B) (hfeas : ∀ s, Prog7Feasible I s ((n s : ℝ) * ε) (Meps s)) :
    ∀ t < K, ∀ b ∈ budgetGrid ε B,
      ∑ s ∈ Finset.univ.filter (fun s : Fin K => t ≤ s.val), (n s : ℝ) * ε ≤ b →
      ∀ D ∈ startSet I S t, l1 (D - prefProd Meps t *ᵥ I.D1) ≤ ε →
        welfare I Meps - 2 * ((K - t : ℕ) : ℝ) * ε * supNorm I.R ≤
          valueFrom I (tab t b D) t D := by sorry

end PipelineInterv.Welfare
