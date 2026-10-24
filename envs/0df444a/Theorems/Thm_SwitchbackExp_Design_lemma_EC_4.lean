-- Prove2me | Theorems.Thm_SwitchbackExp_Design_lemma_EC_4
-- name    : SwitchbackExp.Design.lemma_EC_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T02:30:31.360649+00:00
-- url     : https://prove2.me/theorems/42970e2d-0955-4f95-8d51-7c4bf230e6f7
-- title:
--   Lemma EC.4, p. ec5 — the cross moment E[𝟙_t 𝟙_{t′}] is 0 without overlapping points and (EC.6) otherwise
-- statement:
--   Let $(\mathbb T,\mathbb Q)$ be a regular switchback design with $q_{t_k}\in(0,1)$, let $\mathbb Y$ satisfy Assumptions 1–2, and let $m+1\le t<t'\le T$. Let $O_{\mathbb T}(t,t')=f^m_{\mathbb T}(t)\cap f^m_{\mathbb T}(t')=\{u^o_1<\dots<u^o_{J^o}\}$ be the overlapping randomization points.
--
--   1. If $J^o=0$, then $\mathbb E[\mathbb 1_t\mathbb 1_{t'}]=0$. (EC.5)
--   2. If $J^o\ge1$, then
--   $$\mathbb E[\mathbb 1_t\mathbb 1_{t'}]=\Bigl(\prod_{j=1}^{J^o}\frac1{q_{u^o_j}}-1\Bigr)Y_t(\mathbf 1_{m+1})Y_{t'}(\mathbf 1_{m+1})+Y_t(\mathbf 1_{m+1})Y_{t'}(\mathbf 0_{m+1})+Y_t(\mathbf 0_{m+1})Y_{t'}(\mathbf 1_{m+1})+\Bigl(\prod_{j=1}^{J^o}\frac1{\bar q_{u^o_j}}-1\Bigr)Y_t(\mathbf 0_{m+1})Y_{t'}(\mathbf 0_{m+1}).\qquad\text{(EC.6)}$$
--
--   With Lemma EC.3 this gives the full expansion of the risk used in Lemma 1 and Theorem 1.
--
--   **Formalization Note** The page says $t<t'\in[T]$; the error terms are defined only for periods in $\{m+1,\dots,T\}$, so both $t$ and $t'$ are taken there.
-- source:
--   Bojinov, Simchi-Levi, Zhao, Design and Analysis of Switchback Experiments, arXiv:2009.00148v4 (Management Science 69(7), 2023), Lemma EC.4, p. ec5, (EC.5)–(EC.6)

import Mathlib
import Definitions.Def_SwitchbackExp_Design_Model
import Definitions.Def_SwitchbackExp_Design_Setting

namespace SwitchbackExp.Design

/-- Lemma EC.4 (p. ec5), (EC.5)–(EC.6): the cross moment of the error terms `𝟙_t` and `𝟙_{t′}`. -/
theorem lemma_EC_4 (m T : ℕ) (hmT : m < T) (P : Finset ℕ) (q : ℕ → ℝ)
    (hP : IsRegularPoints T P) (hq : IsRegularProbs P q) (Y : Outcomes)
    (hY1 : NonAnticipating T Y) (hY2 : Carryover m T Y)
    (t t' : ℕ) (ht : t ∈ Finset.Icc (m + 1) T) (ht' : t' ∈ Finset.Icc (m + 1) T) (htt : t < t') :
    (overlap P m t t' = ∅ →
      expect P q (fun w => errTerm m P q Y t w * errTerm m P q Y t' w) = 0) ∧
    ((overlap P m t t').Nonempty →
      expect P q (fun w => errTerm m P q Y t w * errTerm m P q Y t' w)
        = (∏ u ∈ overlap P m t t', 1 / q u - 1) * Y1 Y t * Y1 Y t' + Y1 Y t * Y0 Y t'
          + Y0 Y t * Y1 Y t' + (∏ u ∈ overlap P m t t', 1 / (1 - q u) - 1) * Y0 Y t * Y0 Y t') := by sorry

end SwitchbackExp.Design
