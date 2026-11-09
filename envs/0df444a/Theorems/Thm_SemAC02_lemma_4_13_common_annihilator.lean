-- Prove2me | Theorems.Thm_SemAC02_lemma_4_13_common_annihilator
-- name    : SemAC02.lemma_4_13_common_annihilator
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:29:55.308139+00:00
-- url     : https://prove2.me/theorems/4d9eb1b9-a445-4e5e-929c-2ad7a95aa8cb
-- title:
--   Lemma 4.13 — AC0[2] approximation with a common annihilator
-- statement:
--   Let $d\ge2$ and let $F$ be a family of AC0[2] circuits of depth at most $d$; let $\Gamma$ be the set of distinct rooted subcircuits of circuits in $F$. Let $r,R\ge1$ be integers, $q=Rr^{d-1}$, $\alpha_j=H_n(k-r^{j-1})/(2H_n(k))$ for $j\in[d]$, and assume $r^{d-1}\le k\le n$. There are polynomials $p_A$ ($A\in\Gamma$) and a family $\mathrm{Err}$ of at most $|\Gamma|$ error polynomials such that
--
--   1. $\deg p_A\le r^j$ if $A$ has depth $j<d$, and $\deg p_A\le q$ if $A$ has depth exactly $d$;
--   2. the space $\mathcal A=\{f\in\mathcal B_n^{\le k}: f\,\mathrm{err}=0\ \text{for all }\mathrm{err}\in\mathrm{Err}\}$ satisfies
--   $$
--   \lambda:=\dim\mathcal A\ge(1-\delta)H_n(k),\qquad \delta=|\Gamma|\exp\bigl(-\min\{r\alpha_{d-1},R\alpha_d\}\bigr);
--   $$
--   3. every $f\in\mathcal A$ satisfies $f\,p_A=f\,[\![A]\!]$ for every $A\in\Gamma$.
--
--   The lemma finds one large space of multipliers that makes every subcircuit of a proof behave like a low-degree polynomial.
--
--   Differences from the source:
--   - encoding: AC0[2] circuits with unordered children; size = number of distinct rooted subcircuits → Circ trees with List children; size = number of distinct subterms (proofSize / famSize); reason: a paper circuit is a list presentation of itself with the same evaluation, depth and size; normalising a list circuit or refutation never increases depth or the distinct-subterm count; same instances
--   - encoding: elements of B_n, their degree and products → multilinear MvPolynomial representatives, totalDegree, products ML(f·p) (mulML); reason: every element of B_n has a unique multilinear representative (p.15); same instances
--   - encoding: deg p_A → totalDegree of a representative p A; reason: an element of B_n has degree ≤ D iff it has a representative of total degree ≤ D; p_A enters the conclusion only through products in B_n
-- source:
--   Alekseev, Gryaznov, Itsykson, Pitassi, Robere, Tzameret, Hard Instances for Strong Semantic Proof Systems: CNFs for Depth-Four PC and Deep Instances for AC0[2]-Frege, manuscript (STOC 2027 submission, sha256 c228d68b89b45b5c6c547aa994f7d1799441bb22b2a85e36c6cd400bea8cdb6a), Lemma 4.13, p.34 (PDF p.36)

import Mathlib
import Definitions.Def_SemAC02_Circ
import Definitions.Def_SemAC02_arith
import Definitions.Def_SemAC02_Ble

namespace SemAC02

open Classical in
/-- **Lemma 4.13 (AC0[2]-Frege approximation with a common annihilator)** (Alekseev–Gryaznov–Itsykson–Pitassi–Robere–Tzameret, *Hard Instances for Strong Semantic Proof
Systems*, manuscript (STOC 2027 submission),
Lemma 4.13, p.34): let `d ≥ 2`, and let `F` be a family of AC0[2] circuits of depth at most `d`.
Let `Γ` be the set of distinct rooted subcircuits of circuits in `F`. Choose integers
`r, R ≥ 1`, and set `q = R r^{d−1}` and `α_j = H_n(k − r^{j−1})/(2H_n(k))` for each `j ∈ [d]`.
Assume `r^{d−1} ≤ k ≤ n`. There exist polynomial approximations `p_A` for each `A ∈ Γ` and a
family `Err` of at most `|Γ|` approximation error polynomials with the following properties.

* The degree of `p_A` is at most `r^j` when `A` has depth `j < d`, and it is at most `q` when
  the depth of `A` is exactly `d`.
* Let `𝒜 = {f ∈ B_n^{≤k} : f err = 0 for every err ∈ Err}`. Then
  `λ := dim(𝒜) ≥ (1 − δ) H_n(k)` (7), where `δ = |Γ| exp(−min{r α_{d−1}, R α_d})`.
* Every `f ∈ 𝒜` satisfies `f p_A = f⟦A⟧` for every `A ∈ Γ`.

**Formalization Note** `Γ = F.biUnion subcircuits` (distinct subterms). Products are in `B_n`
(`mulML`); degree of `p_A` is the total degree of a representative. `α_{d−1}` uses
`r^{(d−1)−1} = r^{d−2}`. All subtractions `k − r^{j−1}` are exact since `r^{j−1} ≤ r^{d−1} ≤ k`. -/
theorem lemma_4_13_common_annihilator {n : ℕ} (d : ℕ) (hd : 2 ≤ d) (F : Finset (Circ (Fin n)))
    (hF : ∀ A ∈ F, A.depth ≤ d) (r R k : ℕ) (hr : 1 ≤ r) (hR : 1 ≤ R) (hrk : r ^ (d - 1) ≤ k)
    (hkn : k ≤ n) :
    ∃ (p : Circ (Fin n) → MvPolynomial (Fin n) (ZMod 2))
      (Err : Finset (MvPolynomial (Fin n) (ZMod 2))),
      Err.card ≤ (F.biUnion Circ.subcircuits).card ∧
      (∀ A ∈ F.biUnion Circ.subcircuits, A.depth < d → (p A).totalDegree ≤ r ^ A.depth) ∧
      (∀ A ∈ F.biUnion Circ.subcircuits, A.depth = d → (p A).totalDegree ≤ R * r ^ (d - 1)) ∧
      (1 - ((F.biUnion Circ.subcircuits).card : ℝ) *
          Real.exp (-(min ((r : ℝ) * ((Hn n (k - r ^ (d - 2)) : ℝ) / (2 * (Hn n k : ℝ))))
            ((R : ℝ) * ((Hn n (k - r ^ (d - 1)) : ℝ) / (2 * (Hn n k : ℝ))))))) * (Hn n k : ℝ) ≤
        (Module.finrank (ZMod 2)
          (Ble (Fin n) k ⊓ ⨅ e ∈ Err, LinearMap.ker (mulML e) :
            Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2))) : ℝ) ∧
      ∀ f ∈ (Ble (Fin n) k ⊓ ⨅ e ∈ Err, LinearMap.ker (mulML e) :
          Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2))),
        ∀ A ∈ F.biUnion Circ.subcircuits, mulML f (p A) = mulML f (arith A) := by sorry

end SemAC02
