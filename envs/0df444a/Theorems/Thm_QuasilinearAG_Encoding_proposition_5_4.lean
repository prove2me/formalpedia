-- Prove2me | Theorems.Thm_QuasilinearAG_Encoding_proposition_5_4
-- name    : QuasilinearAG.Encoding.proposition_5_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:43:20.953218+00:00
-- url     : https://prove2.me/theorems/06b4ac0d-919f-47a6-b3c7-b4987b99b971
-- title:
--   Proposition 5.4 — in every intermediate field the $u_{a,j}=C_0^\kappa(m_{a,j})$ are a $k(x_0)$-basis, invert on good fibres, and have a common pole divisor of degree $<(2q+1)D$
-- statement:
--   In the setting of Lemma 5.2 ($q=p^s>2$, $e=p^r$, $V\subset C$ with $|V|=q/e$, $E=F_{h-1}(z)$, $D=eq^{h-1}$), let $\kappa=\lceil\log_q h\rceil+1$, $Q_*=q^\kappa$, and put $u_{a,j}=C_0^\kappa(m_{a,j})$ using the same separator $t=L(x_0)$. These $D$ functions form a basis of $E$ over $k(x_0)$ and evaluate invertibly on every good fibre. Their poles are contained in a common effective divisor of degree strictly less than $(2q+1)D$, disjoint from those fibres.
--
--   Differences from the source:
--   - encoding: the tower F_h of (3.1) over k = F_{q^2}, q = p^s > 2 → any field F over any finite field k with q^2 elements (IsPrimePow q, 2 < q), with x_0 transcendental, (x_i^q + x_i)(1 + x_{i-1}^{q-1}) = x_{i-1}^q for 1 ≤ i ≤ h, and F = k(x_0, …, x_h) (IsGSTower); reason: every such F is a model of F_h; the division in φ is cleared, which excludes no instance
--   - encoding: places P and ord_P normalized to value group Z → Place k F: additive valuations F → Z ∪ {∞}, onto Z, zero on k^×; reason: places of a function field correspond one to one to their normalized valuations
--   - encoding: an F_p-subspace V ⊂ C of size q/e, e ∈ {p, …, q} → an additive subgroup V of k contained in {v : v^q + v = 0} with Nat.card V = q/e, e = p^r, 1 ≤ r ≤ s; reason: in characteristic p additive subgroups are exactly the F_p-subspaces
--   - encoding: basis over k(x_0); evaluate invertibly on every good fibre; common effective divisor disjoint from the fibres → linear independence and span ⊤ over k(x_0) inside E; bijectivity of c ↦ (P ↦ Σ c_{a,j} u_{a,j}(P)) on the places of E above good β; ∃ A ≥ 0 of finite support with divDeg A < (2q+1)D, ord_P u_{a,j} ≥ −A(P), A(P) = 0 above good β; reason: Lean names for the same statements
-- source:
--   Chao, Liu, Li, Ma, Wang, Quasilinear Encoding at the Quadratic Alphabet Scale via Short Cartier Bases, STOC 2027 submission (manuscript sha256 355c15dc…), p. 19, Proposition 5.4 (PDF p. 21)

import Mathlib
import Definitions.Def_QuasilinearAG_Encoding_Tower
import Definitions.Def_QuasilinearAG_Encoding_Intermediate

namespace QuasilinearAG.Encoding

/-- Proposition 5.4 (Short extraction in every intermediate field), p. 19 (PDF 21). In the setting
of Lemma 5.2 (`q = p^s > 2`, `e = p^r`, `1 ≤ r ≤ s`, `V ⊂ C` with `|V| = q/e`, `E = F_{h-1}(z)`,
`D = e q^{h-1}`), let `κ = ⌈log_q h⌉ + 1`, `Q* = q^κ` and `u_{a,j} = C₀^κ(m_{a,j})` with the same
separator `t = L(x₀)`. These `D` functions form a basis of `E` over `k(x₀)` and evaluate invertibly
on every good fibre; their poles are contained in a common effective divisor of degree strictly
less than `(2q + 1)D`, disjoint from those fibres. -/
theorem proposition_5_4 {k F : Type*} [Field k] [Fintype k] [Field F] [Algebra k F]
    (p s q h : ℕ) [Fact p.Prime] (hqs : q = p ^ s) (hq2 : 2 < q) (hk : Fintype.card k = q ^ 2)
    (hh : 1 ≤ h) (x : ℕ → F) (hx : IsGSTower k q h x)
    (r e : ℕ) (hr1 : 1 ≤ r) (hrs : r ≤ s) (he : e = p ^ r)
    (V : AddSubgroup k) (hVC : ∀ v ∈ V, v ^ q + v = 0) (hVcard : Nat.card V = q / e) :
    LinearIndependent (IntermediateField.adjoin k {x0InE h x V}) (interExtracted q h e x V) ∧
      Submodule.span (IntermediateField.adjoin k {x0InE h x V})
          (Set.range (interExtracted q h e x V)) = ⊤ ∧
      (∀ β : k, IsGood q β →
        Function.Bijective (fibreEvalMap (x0InE h x V) β (interExtracted q h e x V))) ∧
      ∃ A : Place k (interField h x V) → ℤ, (∀ P, 0 ≤ A P) ∧ (Function.support A).Finite ∧
        divDeg A < (2 * (q : ℤ) + 1) * ((e : ℤ) * (q : ℤ) ^ (h - 1)) ∧
        (∀ aj (P : Place k (interField h x V)),
          ((-A P : ℤ) : WithTop ℤ) ≤ P.v (interExtracted q h e x V aj)) ∧
        ∀ β : k, IsGood q β → ∀ P : Place k (interField h x V),
          P.Above (x0InE h x V) β → A P = 0 := by sorry

end QuasilinearAG.Encoding
