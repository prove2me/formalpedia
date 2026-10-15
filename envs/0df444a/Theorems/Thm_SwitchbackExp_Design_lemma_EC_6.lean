-- Prove2me | Theorems.Thm_SwitchbackExp_Design_lemma_EC_6
-- name    : SwitchbackExp.Design.lemma_EC_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:30:48.309193+00:00
-- url     : https://prove2.me/theorems/e2d893b9-3fd8-4d40-9b42-45099f99c661
-- title:
--   Lemma EC.6, p. ec10 — at 𝕐 = 𝕐± with fair coins, E[𝟙_t²] = 2^{J+1}B² and E[𝟙_t 𝟙_{t′}] = 0 or 2^{J^o+1}B²
-- statement:
--   Let $B>0$, let $\mathbb T$ be regular randomization points, and let every coin be fair, $q_0=\dots=q_K=1/2$. Let $\mathbb Y=\mathbb Y^+$ or $\mathbb Y=\mathbb Y^-$. For $t\in\{m+1,\dots,T\}$ with $J=|f^m_{\mathbb T}(t)|$,
--   $$\mathbb E[\mathbb 1_t^2]=2^{J+1}B^2 .$$
--   For $m+1\le t<t'\le T$ with $J^o=|O_{\mathbb T}(t,t')|$: if $J^o=0$ then $\mathbb E[\mathbb 1_t\mathbb 1_{t'}]=0$, and if $J^o\ge1$ then
--   $$\mathbb E[\mathbb 1_t\mathbb 1_{t'}]=2^{J^o+1}B^2 .$$
--
--   These moments turn the risk of a fair-coin design at the extreme outcomes into a combinatorial function of the randomization points, the starting point of Lemmas EC.7–EC.9.
--
--   **Formalization Note** The periods are restricted to $\{m+1,\dots,T\}$, where the error terms are defined (the page writes $t\in[T]$).
-- source:
--   Bojinov, Simchi-Levi, Zhao, Design and Analysis of Switchback Experiments, arXiv:2009.00148v4 (Management Science 69(7), 2023), Lemma EC.6, p. ec10

import Mathlib
import Definitions.Def_SwitchbackExp_Design_Model
import Definitions.Def_SwitchbackExp_Design_Setting

namespace SwitchbackExp.Design

/-- Lemma EC.6 (p. ec10): the moments of the error terms at `𝕐 = 𝕐⁺` or `𝕐 = 𝕐⁻` with fair coins. -/
theorem lemma_EC_6 (m T : ℕ) (hmT : m < T) (B : ℝ) (hB : 0 < B) (P : Finset ℕ)
    (hP : IsRegularPoints T P) (Y : Outcomes) (hYpm : Y = Yplus B ∨ Y = Yminus B) (t t' : ℕ)
    (ht : t ∈ Finset.Icc (m + 1) T) (ht' : t' ∈ Finset.Icc (m + 1) T) :
    expect P half (fun w => errTerm m P half Y t w ^ 2) = 2 ^ ((detPoints P m t).card + 1) * B ^ 2 ∧
    (t < t' → overlap P m t t' = ∅ →
      expect P half (fun w => errTerm m P half Y t w * errTerm m P half Y t' w) = 0) ∧
    (t < t' → (overlap P m t t').Nonempty →
      expect P half (fun w => errTerm m P half Y t w * errTerm m P half Y t' w)
        = 2 ^ ((overlap P m t t').card + 1) * B ^ 2) := by sorry

end SwitchbackExp.Design
