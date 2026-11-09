-- Prove2me | Theorems.Thm_SemAC02_lemma_4_14_simulation_after_multiplication
-- name    : SemAC02.lemma_4_14_simulation_after_multiplication
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:30:12.400698+00:00
-- url     : https://prove2.me/theorems/ea547295-e968-4ff3-93e0-1780ff0170b5
-- title:
--   Lemma 4.14 — simulation after multiplication
-- statement:
--   Let $\pi$ be a semantic AC0[2]-Frege refutation of a family $F$ (of any depth). Suppose every proof line $A$ has an approximation $p_A$ of degree at most $q$, and let $f\in\mathcal B_n^{\le k}$ satisfy $f\,p_A=f\,[\![A]\!]$ for every proof line $A$. Then there is a PC derivation of $f$ from
--   $$
--   \{f\,[\![A]\!]: A\in F\}
--   $$
--   in which every line has the form $fQ_i$ with $Q_i\in\mathcal B_n$, $\deg Q_i\le3q$. In particular the derivation has degree at most $k+3q$.
--
--   Multiplying a refutation by a common annihilator thus produces a low-degree PC derivation of the multiplier itself.
--
--   Differences from the source:
--   - encoding: AC0[2] circuits with unordered children; size = number of distinct rooted subcircuits → Circ trees with List children; size = number of distinct subterms (proofSize / famSize); reason: a paper circuit is a list presentation of itself with the same evaluation, depth and size; normalising a list circuit or refutation never increases depth or the distinct-subterm count; same instances
--   - encoding: elements of B_n, their degree and products → multilinear MvPolynomial representatives, totalDegree, products ML(f·p) (mulML); reason: every element of B_n has a unique multilinear representative (p.15); same instances
--   - encoding: PC derivation in B_n; "a derivation of g" → PCNonBool.IsDerivation with reduction AC02Frege.ML; g occurs as a line; reason: lines are the multilinear representatives; the extra axiom multiple 0·a only adds zero lines, which can be deleted without changing any other line or degree
-- source:
--   Alekseev, Gryaznov, Itsykson, Pitassi, Robere, Tzameret, Hard Instances for Strong Semantic Proof Systems: CNFs for Depth-Four PC and Deep Instances for AC0[2]-Frege, manuscript (STOC 2027 submission, sha256 c228d68b89b45b5c6c547aa994f7d1799441bb22b2a85e36c6cd400bea8cdb6a), Lemma 4.14, p.35 (PDF p.37)

import Mathlib
import Definitions.Def_SemAC02_Circ
import Definitions.Def_SemAC02_IsSemRefutation
import Definitions.Def_SemAC02_arith
import Definitions.Def_SemAC02_Ble
import Definitions.Def_PCNonBool_IsDerivation
import Definitions.Def_AC02Frege_ML

namespace SemAC02

/-- **Lemma 4.14 (Simulation after multiplication)** (Alekseev–Gryaznov–Itsykson–Pitassi–Robere–Tzameret, *Hard Instances for Strong Semantic Proof
Systems*, manuscript (STOC 2027 submission), Lemma 4.14, p.35): let `π`
be a semantic AC0[2]-Frege refutation of `F`. Suppose the arithmetisation of each proof line `A`
has a polynomial approximation `p_A` of degree at most `q`. If `f ∈ B_n^{≤k}` satisfies
`f p_A = f⟦A⟧` for every proof line, then there is a PC derivation of `f` from
`{f⟦A⟧ : A ∈ F}`, in which every line has the form `f Q_i` for some `Q_i ∈ B_n` with
`deg Q_i ≤ 3q`. In particular, the derivation has degree at most `k + 3q`.

**Formalization Note** The refutation may have any depth `d`. Products are in `B_n` (`mulML`).
The PC derivation is the published `PCNonBool.IsDerivation` with reduction `AC02Frege.ML` from
the axioms `f⟦A⟧`, `A ∈ F`, containing `f`; degrees are total degrees of representatives. -/
theorem lemma_4_14_simulation_after_multiplication {n : ℕ} (F : Set (Circ (Fin n))) (d : ℕ)
    (π : List (Circ (Fin n))) (hπ : IsSemRefutation d F π) (q k : ℕ)
    (p : Circ (Fin n) → MvPolynomial (Fin n) (ZMod 2)) (hp : ∀ A ∈ π, (p A).totalDegree ≤ q)
    (f : MvPolynomial (Fin n) (ZMod 2)) (hf : f ∈ Ble (Fin n) k)
    (hfp : ∀ A ∈ π, mulML f (p A) = mulML f (arith A)) :
    ∃ τ : List (MvPolynomial (Fin n) (ZMod 2)),
      PCNonBool.IsDerivation AC02Frege.ML (mulML f '' (arith '' F)) τ ∧ f ∈ τ ∧
      (∀ u ∈ τ, ∃ Q : MvPolynomial (Fin n) (ZMod 2), Q.totalDegree ≤ 3 * q ∧ u = mulML f Q) ∧
      ∀ u ∈ τ, u.totalDegree ≤ k + 3 * q := by sorry

end SemAC02
