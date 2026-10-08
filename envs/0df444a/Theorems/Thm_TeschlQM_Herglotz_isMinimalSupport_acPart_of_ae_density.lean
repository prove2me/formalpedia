-- Prove2me | Theorems.Thm_TeschlQM_Herglotz_isMinimalSupport_acPart_of_ae_density
-- name    : TeschlQM.Herglotz.isMinimalSupport_acPart_of_ae_density
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-07T22:07:46.999188+00:00
-- url     : https://prove2.me/theorems/dbd992e8-681c-42cc-85b2-1f75f82f1bf2
-- title:
--   Positive finite density characterizes a minimal support up to Lebesgue-null sets
-- statement:
--   Let $\mu$ be a finite Borel measure on $\mathbb R$, with $f=d\mu_{ac}/d\lambda$. Suppose $S\subseteq\mathbb R$ agrees Lebesgue-almost everywhere with the set $\{t:0<f(t)<\infty\}$. Then $S$ is a minimal support for $\mu_{ac}$:
--
--   $$\mu_{ac}(S^c)=0,\qquad M\subseteq S,\ M\text{ Borel},\ \mu_{ac}(M)=0\Longrightarrow\lambda(M)=0.$$
--
--   This null-set invariant form of Lemma A.39 can transfer density supports to boundary-limit supports.
-- source:
--   G. Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99 (2009), Theorems A.37–A.38, p. 286, Lemma A.39, p. 287, and Theorems 3.22–3.23, pp. 108–109; https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf (PDF pp. 119–120, 297–298).

import Definitions.Def_TeschlQM_Herglotz_acPart
import Definitions.Def_TeschlQM_Herglotz_IsMinimalSupport

open MeasureTheory Filter
open scoped ENNReal Topology
open TeschlQM.Herglotz

theorem TeschlQM.Herglotz.isMinimalSupport_acPart_of_ae_density (μ : Measure ℝ) [IsFiniteMeasure μ] (S : Set ℝ)
    (hS : ∀ᵐ t ∂(volume : Measure ℝ),
      t ∈ S ↔ 0 < μ.rnDeriv volume t ∧ μ.rnDeriv volume t < ⊤) :
    IsMinimalSupport (acPart μ) S := by sorry
