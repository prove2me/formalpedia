-- Prove2me | Theorems.Thm_WeightedMajority_Anomalies_theorem_8_1
-- name    : WeightedMajority.Anomalies.theorem_8_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:40:01.520825+00:00
-- url     : https://prove2.me/theorems/65e6b9aa-7912-4c80-a631-7cf7f9ebd03e
-- title:
--   Theorem 8.1 — with η anomalies, opt(F, η) ≥ opt(F, 0) + 2η for every class with |F| > 1
-- statement:
--   Let $X$ be an arbitrary domain and $F$ a class of $\{0,1\}$-valued functions on $X$, possibly infinite, with at least two members. For $\eta \in \{0,1,2,\dots\}$ let $\mathrm{opt}(F,\eta)$ be the minimum, over all deterministic on-line prediction algorithms $A$, of the maximum number of mistakes $A$ makes on a finite sequence of trials having at most $\eta$ anomalies with respect to $F$ (some $f \in F$ disagrees with at most $\eta$ of its labels). Then
--
--   $$\mathrm{opt}(F,\eta) \ \ge\ \mathrm{opt}(F,0) + 2\eta .$$
--
--   Each anomaly the adversary is allowed therefore costs every deterministic learner at least two additional mistakes beyond the optimal noise-free bound. The theorem shows that the deterministic Weighted Majority algorithm, whose mistake bound grows at a rate that can be made arbitrarily close to $2$ per anomaly by the choice of $\beta$, has an essentially optimal rate of growth in the number of anomalies.
--
--   **Formalization Note** Values are in $\mathbb N \cup \{\infty\}$ (`ℕ∞`); when $\mathrm{opt}(F,0) = \infty$ the statement says $\mathrm{opt}(F,\eta) = \infty$. The hypothesis $|F| > 1$ is `F.Nontrivial` (two distinct members), which also covers infinite classes.
-- source:
--   Littlestone, Warmuth, The Weighted Majority Algorithm, Inform. and Comput. 108 (1994), p. 250, Theorem 8.1

import Mathlib
import Definitions.Def_UnderstandingML_Online
import Definitions.Def_WeightedMajority_Anomalies_Opt

namespace WeightedMajority.Anomalies

/-- Littlestone and Warmuth's Theorem 8.1 (p. 250): for every class `F` of `{0,1}`-valued
functions with `|F| > 1` and every `η ≥ 0`, `opt(F, η) ≥ opt(F, 0) + 2η`. -/
theorem theorem_8_1 {X : Type*} (F : Set (X → Bool)) (hF : F.Nontrivial) (η : ℕ) :
    opt F 0 + 2 * (η : ℕ∞) ≤ opt F η := by sorry

end WeightedMajority.Anomalies
