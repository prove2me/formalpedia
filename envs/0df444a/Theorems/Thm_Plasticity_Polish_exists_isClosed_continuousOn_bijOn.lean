-- Prove2me | Theorems.Thm_Plasticity_Polish_exists_isClosed_continuousOn_bijOn
-- name    : Plasticity.Polish.exists_isClosed_continuousOn_bijOn
-- status  : Proved
-- author  : @scanstone
-- created : 2026-11-18T20:09:00.923732+00:00
-- url     : https://prove2.me/theorems/d4be51df-cf58-48dd-9944-b2c0dcfe89f2
-- title:
--   Every Borel subset of a Polish space is a continuous injective image of a closed subset of Baire space
-- statement:
--   Let $Y$ be a nonempty Polish space and $M\subseteq Y$ a Borel set.
--   There are a closed set $C\subseteq\mathbb N^{\mathbb N}$ and a map $\varphi\colon\mathbb N^{\mathbb N}\to Y$ that is continuous on $C$ and maps $C$ bijectively onto $M$.
-- source:
--   A. S. Kechris, Classical Descriptive Set Theory, Springer GTM 156 (1995), Theorem 13.7 with Theorem 7.9; Y. N. Moschovakis, Descriptive Set Theory, 2nd ed. (2009), 2E.8–2E.9

import Mathlib.MeasureTheory.Constructions.Polish.Basic

namespace Plasticity
theorem Polish.exists_isClosed_continuousOn_bijOn {Y : Type*} [TopologicalSpace Y] [PolishSpace Y] [Nonempty Y]
    [MeasurableSpace Y] [BorelSpace Y] (M : Set Y) (hM : MeasurableSet M) :
    ∃ C : Set (ℕ → ℕ), IsClosed C ∧ ∃ φ : (ℕ → ℕ) → Y, ContinuousOn φ C ∧ Set.BijOn φ C M := by sorry
end Plasticity
