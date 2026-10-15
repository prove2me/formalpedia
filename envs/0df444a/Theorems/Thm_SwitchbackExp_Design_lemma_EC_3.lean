-- Prove2me | Theorems.Thm_SwitchbackExp_Design_lemma_EC_3
-- name    : SwitchbackExp.Design.lemma_EC_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:30:10.898857+00:00
-- url     : https://prove2.me/theorems/ebf5cd94-7e0a-4f40-9ffd-ac5e9c1e090b
-- title:
--   Lemma EC.3, p. ec4 — the second moment E[𝟙_t²] of the error term (EC.4)
-- statement:
--   Let $(\mathbb T,\mathbb Q)$ be a regular switchback design with $q_{t_k}\in(0,1)$, let $\mathbb Y$ satisfy Assumptions 1–2, and let $t\in\{m+1,\dots,T\}$. Write $f^m_{\mathbb T}(t)=\{u_1<\dots<u_J\}$ for the determining randomization points of the periods $t-m,\dots,t$, and $\bar q=1-q$. Then the error term $\mathbb 1_t$ of (EC.2) satisfies
--   $$\mathbb E[\mathbb 1_t^2]=\Bigl(\prod_{j=1}^J\frac1{q_{u_j}}-1\Bigr)Y_t(\mathbf 1_{m+1})^2+2\,Y_t(\mathbf 1_{m+1})Y_t(\mathbf 0_{m+1})+\Bigl(\prod_{j=1}^J\frac1{\bar q_{u_j}}-1\Bigr)Y_t(\mathbf 0_{m+1})^2.$$
--
--   Together with Lemma EC.4 this expands the risk $(T-m)^2\,r(\eta_{\mathbb T,\mathbb Q},\mathbb Y)=\sum_{t,t'}\mathbb E[\mathbb 1_t\mathbb 1_{t'}]$ into a quadratic form in the outcomes with nonnegative coefficients.
--
--   **Formalization Note** The page says "for any $t\in[T]$", but $\mathbb 1_t$ is defined in (EC.2) only for $t\in\{m+1,\dots,T\}$; the statement is restricted to that range.
-- source:
--   Bojinov, Simchi-Levi, Zhao, Design and Analysis of Switchback Experiments, arXiv:2009.00148v4 (Management Science 69(7), 2023), Lemma EC.3, p. ec4, (EC.4); notation EC.3.1, p. ec3, (EC.2)

import Mathlib
import Definitions.Def_SwitchbackExp_Design_Model
import Definitions.Def_SwitchbackExp_Design_Setting

namespace SwitchbackExp.Design

/-- Lemma EC.3 (p. ec4), (EC.4): the second moment of the error term `𝟙_t`. -/
theorem lemma_EC_3 (m T : ℕ) (hmT : m < T) (P : Finset ℕ) (q : ℕ → ℝ)
    (hP : IsRegularPoints T P) (hq : IsRegularProbs P q) (Y : Outcomes)
    (hY1 : NonAnticipating T Y) (hY2 : Carryover m T Y)
    (t : ℕ) (ht : t ∈ Finset.Icc (m + 1) T) :
    expect P q (fun w => errTerm m P q Y t w ^ 2)
      = (∏ u ∈ detPoints P m t, 1 / q u - 1) * Y1 Y t ^ 2 + 2 * Y1 Y t * Y0 Y t
        + (∏ u ∈ detPoints P m t, 1 / (1 - q u) - 1) * Y0 Y t ^ 2 := by sorry

end SwitchbackExp.Design
