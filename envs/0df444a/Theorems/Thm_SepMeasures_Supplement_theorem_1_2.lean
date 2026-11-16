-- Prove2me | Theorems.Thm_SepMeasures_Supplement_theorem_1_2
-- name    : SepMeasures.Supplement.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:16:34.212946+00:00
-- url     : https://prove2.me/theorems/95df75d9-9e51-431e-b6f9-34a30b749c14
-- title:
--   Theorem 1.2 — measure equivalence $\alpha(\mathcal P^d)=\alpha(\mathcal P^d_b)=\alpha(\mathcal P^d_{bc})=\alpha(\mathcal P^d_{\mathbb N})$
-- statement:
--   Let $d\ge1$ and let $\|\cdot\|$ be any norm on $\mathbb R^d$. Consider the following families of pairs $(\mu,\nu)$ of probability measures on $\mathbb R^d$:
--
--   1. $\mathcal P^d$: finite first moments, disjoint atom sets whose union is in affine general position, and non-atomic parts that give zero mass to every affine hyperplane;
--   2. $\mathcal P^d_b\subseteq\mathcal P^d$: the pairs in which both measures have bounded support;
--   3. $\mathcal P^d_{bc}\subseteq\mathcal P^d_b$: the pairs in which both measures are moreover absolutely continuous with respect to Lebesgue measure;
--   4. $\mathcal P^d_{\mathbb N}=\bigcup_{n\ge1}\mathcal P^d_n\subseteq\mathcal P^d$: the pairs in which both measures are uniform on sets of the same number $n$ of points.
--
--   For a family $F$ write $\alpha(F)=\inf_{(\mu,\nu)\in F,\,L_{\mu,\nu}>0}\sup_{H}C_{\mu,\nu}(H)/L_{\mu,\nu}$, where $L_{\mu,\nu}=\mathbb E\|X-Y\|$ and $C_{\mu,\nu}(H)$ is the part of it carried by pairs strictly separated by the affine hyperplane $H$. Then
--   $$\alpha(\mathcal P^d)=\alpha(\mathcal P^d_b)=\alpha(\mathcal P^d_{bc})=\alpha(\mathcal P^d_{\mathbb N}).$$
--
--   This equivalence lets bounds proved for one family, for instance compactly supported absolutely continuous measures or finite point sets, transfer to all the others.
--
--   **Formalization Note** The chain is stated as the three equalities of consecutive terms. The carrier is `EuclideanSpace ℝ (Fin d)` with an arbitrary seminorm $N$ satisfying $N(x)=0\Rightarrow x=0$. $\mathcal P^d$, $\mathcal P^d_b$, $\mathcal P^d_{bc}$ and $\alpha$ are the published `SepMeasures.P`, `Pb`, `Pbc` and `cutRatio`; $\mathcal P^d_{\mathbb N}$ is `SepMeasures.Supplement.PN`. Every family contains pairs with $L>0$ for $d\ge1$, so no side is an infimum over the empty set.
--
--   Differences from the source:
--   - encoding: a norm on ℝ^d → a seminorm N on EuclideanSpace ℝ (Fin d) with N x = 0 → x = 0; reason: Lean convention for an arbitrary (non-Euclidean) norm on the Euclidean carrier; same instances
--   - encoding: the chain α(𝒫^d) = α(𝒫^d_b) = α(𝒫^d_bc) = α(𝒫^d_N) → the conjunction of the three consecutive equalities; reason: Lean has no chained equality; same content
-- source:
--   Correa–Griesbach–Harb–Hommelsheim–Jlibene–Livanos–Solan, Separating Measures by Hyperplanes (manuscript, STOC 2027 submission, sha256 96a8692407ff1815980863f3baa9c5d7b90ba27e781ed19063306f67d26fa82f), Theorem 1.2, p.5 (restated p.44, proved §6, pp.44–55); families Definition 2.2, p.12

import Mathlib
import Definitions.Def_SepMeasures_CutValue
import Definitions.Def_SepMeasures_Families
import Definitions.Def_SepMeasures_Supplement_UniformFamilies

open MeasureTheory

namespace SepMeasures

namespace Supplement

/-- Correa–Griesbach–Harb–Hommelsheim–Jlibene–Livanos–Solan, *Separating Measures by Hyperplanes*
(manuscript, sha256 96a86924…fa82f), Theorem 1.2, p.5 (restated p.44, proved §6, pp.44–55): for
every `d ≥ 1` and every norm on `ℝ^d`, `α(𝒫^d) = α(𝒫^d_b) = α(𝒫^d_bc) = α(𝒫^d_N)`.

**Formalization Note.** The chain of equalities is written as three equalities of consecutive
terms. The norm is a `Seminorm` `N` on `EuclideanSpace ℝ (Fin d)` with `N x = 0 → x = 0`.
`P`, `Pb`, `Pbc` and `cutRatio` are the published definitions; `PN` is `⋃_{n ≥ 1} 𝒫^d_n` with
both measures uniform on `n` distinct points. Each of the four families contains a pair with
`L > 0` for `d ≥ 1` (the pair `(δ₀, δ_e)` lies in `𝒫^d_b` and in `𝒫^d_1`; two uniform measures on
disjoint balls lie in `𝒫^d_bc`), so no side is Lean's empty-index value `0`. -/
theorem theorem_1_2 (d : ℕ) (hd : 1 ≤ d) (N : Seminorm ℝ (E d)) (hN : ∀ x, N x = 0 → x = 0) :
    cutRatio N (P d N) = cutRatio N (Pb d N) ∧
    cutRatio N (Pb d N) = cutRatio N (Pbc d N) ∧
    cutRatio N (Pbc d N) = cutRatio N (PN d N) := by sorry

end Supplement

end SepMeasures
