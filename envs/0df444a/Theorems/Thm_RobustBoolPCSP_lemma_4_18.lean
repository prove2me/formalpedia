-- Prove2me | Theorems.Thm_RobustBoolPCSP_lemma_4_18
-- name    : RobustBoolPCSP.lemma_4_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:26:31.334095+00:00
-- url     : https://prove2.me/theorems/330a3650-361a-48d5-b09b-d5c0353743d2
-- title:
--   Lemma 4.18 (Witness normal form)
-- statement:
--   Let $\Gamma$ be a finite Boolean symmetric template with $P_j\subseteq Q_j$ for every $j$. Suppose that no single pair of $\Gamma$ fails both the odd Majority family and the odd Alternating Threshold family, but some pair fails an odd Majority and some pair fails an odd Alternating Threshold. Then, after global negation of individual pairs, $\Gamma$ contains two distinct pairs $R_{\mathsf A}$ and $R_{\mathsf M}$ such that
--
--   1. $R_{\mathsf A}=(\mathrm{Ham}_n(\{a\}),Q_{\mathsf A})$ with $n/2<a<n$ and $Q_{\mathsf A}\in\{\mathrm{NAND}_n,\mathrm{NAE}_n\}$;
--   2. $R_{\mathsf M}=(\mathrm{Ham}_{n}(S),Q_{\mathsf M})$, of some arity $n$, with $S\subseteq\{0,\dots,\lfloor n/2\rfloor\}$ and $\beta=\max S\ge1$; every weight missing from $Q_{\mathsf M}$ is at least $2\beta$; if $\beta=n/2$ then $S$ contains a smaller level; and $R_{\mathsf M}$ is preserved by every odd Majority but not by every odd Alternating Threshold.
--
--   The normal form feeds the simulations of Lemma 4.20.
--
--   Differences from the source:
--   - encoding: relation pairs indexed by [m] → relation pairs indexed by a finite type ι; reason: a finite index type is in bijection with [m]
--   - encoding: tuples in sign notation {−1, 1}^n, weight = number of +1 entries → Boolean tuples Fin n → Bool with true = +1, weight hw = number of true entries; sums use sgnVec; reason: the identification 0 ↔ −1, 1 ↔ +1 of §3.2
--   - encoding: after global negation of individual pairs, Γ contains distinct pairs R_A and R_M → indices j_A ≠ j_M and flags ε_A, ε_M such that the pair j_A (negated iff ε_A) has property (i) and the pair j_M (negated iff ε_M) has property (ii); reason: global negation (−P, −Q) of p.25; distinct pairs are pairs at distinct indices
--   - reading: every weight missing from Q_M → every w ≤ n such that no tuple of weight w lies in Q_M; reason: Q_M is symmetric, so a weight is either wholly in or wholly out
-- source:
--   Cai, Jiang, Zou, On Robust Promise CSPs: A Boolean Dichotomy, Sharp Quantitative Bounds, and Soft-Equality Transfer, STOC 2027 submission (manuscript of 2026-11-03, sha256 fd1be0d0624155f00f7a115874a4dadfb7ebb2d4187530c7d0bdd4e1406e8732), §4.4, Lemma 4.18, p.25

import Mathlib
import Definitions.Def_RobustBoolPCSP_Signed
import Definitions.Def_RobustBoolPCSP_WitnessPairs
import Definitions.Def_RobustBoolPCSP_Simulation

set_option autoImplicit false

namespace RobustBoolPCSP

open SymBoolPCSP.CFixing in
/-- **Lemma 4.18 (Witness normal form)**, p.25. Cai, Jiang, Zou, *On Robust Promise CSPs*, STOC 2027 submission (manuscript of 2026-11-03,
sha256 fd1be0d0…).
"Let Γ be symmetric with Pj ⊆ Qj, and suppose that no single pair of Γ fails both families, but some
pair fails an odd Majority and some pair fails an odd Alternating Threshold. Then, after global
negation of individual pairs, Γ contains distinct pairs RA and RM with the following properties.
(i) RA = (Hamn({a}), QA) with n/2 < a < n and QA ∈ {NANDn, NAEn}. (ii) RM = (Hamn(S), QM), of some
arity n, with S ⊆ {0, . . . , ⌊n/2⌋} and β = max S ≥ 1; every weight missing from QM is at least 2β;
if β = n/2, then S contains a smaller level; and RM is preserved by every odd Majority but not by
every odd Alternating Threshold."

**Formalization Note.** "Distinct pairs" are pairs with distinct indices `jA ≠ jM`. Global negation
of a pair `(P, Q)` is `(−P, −Q)` (p.25), applied to the pair `j` when the flag `ε_j` is `true`
(`negIf`). Properties (i), (ii) are `IsWitnessRA`, `IsWitnessRM`. -/
theorem lemma_4_18 {ι : Type} [Fintype ι] (Γ : Template ι Bool Bool)
    (hsym : IsSymmetricTemplate Γ) (hprom : IsPromiseTemplate Γ)
    (hnone : ∀ j, (∀ L : ℕ, Odd L → PolOf (Γ.P j) (Γ.Q j) (Maj L)) ∨
      (∀ L : ℕ, Odd L → PolOf (Γ.P j) (Γ.Q j) (AT L)))
    (hMaj : ∃ j, ∃ L : ℕ, Odd L ∧ ¬ PolOf (Γ.P j) (Γ.Q j) (Maj L))
    (hAT : ∃ j, ∃ L : ℕ, Odd L ∧ ¬ PolOf (Γ.P j) (Γ.Q j) (AT L)) :
    ∃ (jA jM : ι) (εA εM : Bool), jA ≠ jM ∧
      IsWitnessRA (negIf εA (Γ.P jA)) (negIf εA (Γ.Q jA)) ∧
      IsWitnessRM (negIf εM (Γ.P jM)) (negIf εM (Γ.Q jM)) := by sorry

end RobustBoolPCSP
