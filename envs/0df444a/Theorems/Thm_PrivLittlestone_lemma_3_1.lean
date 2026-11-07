-- Prove2me | Theorems.Thm_PrivLittlestone_lemma_3_1
-- name    : PrivLittlestone.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:33:45.38051+00:00
-- url     : https://prove2.me/theorems/ff871cf3-80aa-4a19-b79e-7e8c33bc40ba
-- title:
--   Lemma 3.1 — one insertion adds mass at most $\gamma Z_S$, so $Z_{S'} \le (1+\gamma)Z_S$
-- statement:
--   Let a ranked candidate system of height $D$ and branching parameter $B$ be given, and let $\eta, a > 0$. Suppose $S' = Su$ appends one record $u$ to $S$, and put $\gamma = e^{\eta}\sum_{j=1}^{D} B^j e^{-aj}$. Then
--   $$
--   \sum_{g \in C(S') \setminus C(S)} w_{S'}(g) \le \gamma Z_S, \qquad Z_{S'} \le (1 + \gamma) Z_S .
--   $$
--   If $B e^{-a} < 1$, then $\gamma \le \dfrac{e^{\eta} B e^{-a}}{1 - B e^{-a}}$.
--
--   This is the one-step estimate behind the batch inequality (Lemma 3.2).
--
--   Differences from the source: none.
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), Lemma 3.1, p.5

import Mathlib
import Definitions.Def_PrivLittlestone_potential
import Definitions.Def_PrivLittlestone_gammaTerm

namespace PrivLittlestone

open Classical in
/-- **Lemma 3.1 (Mass introduced by one insertion)** (He–He, *Private Online Learning of
Littlestone Classes and Matroid Flats*, STOC 2027 submission manuscript (sha256
21480556…c562), Lemma 3.1, p.5). For a ranked candidate system and `η, a > 0`, if `S' = Su`
appends one record and `γ = e^η ∑_{j=1}^D B^j e^{−aj}`, then
`∑_{g ∈ C(S') \ C(S)} w_{S'}(g) ≤ γ Z_S`, `Z_{S'} ≤ (1 + γ) Z_S`, and, if `B e^{−a} < 1`,
`γ ≤ e^η B e^{−a}/(1 − B e^{−a})`. -/
theorem lemma_3_1 {Z U : Type*} {D : ℕ} {B : ℝ} (sys : RankedCandidateSystem Z U D B)
    (η a : ℝ) (hη : 0 < η) (ha : 0 < a) (S : List Z) (u : Z) :
    (∑ g ∈ sys.C (S ++ [u]) \ sys.C S, weight sys η a (S ++ [u]) g) ≤
        gammaTerm η a B D * potential sys η a S ∧
      potential sys η a (S ++ [u]) ≤ (1 + gammaTerm η a B D) * potential sys η a S ∧
      (B * Real.exp (-a) < 1 →
        gammaTerm η a B D ≤ Real.exp η * B * Real.exp (-a) / (1 - B * Real.exp (-a))) := by sorry

end PrivLittlestone
