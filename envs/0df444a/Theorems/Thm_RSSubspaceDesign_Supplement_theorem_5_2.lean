-- Prove2me | Theorems.Thm_RSSubspaceDesign_Supplement_theorem_5_2
-- name    : RSSubspaceDesign.Supplement.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T20:42:03.014121+00:00
-- url     : https://prove2.me/theorems/fef24f62-5c8f-483a-b7fa-881a709dbcd9
-- title:
--   Theorem 5.2 — in time $\mathrm{poly}(n,g,\log|F|)$, a $K(X)$-space of dimension $\le 2/\varepsilon$ containing every message with $\ge k+\varepsilon n$ agreements
-- statement:
--   Fix $0 < \varepsilon < 1/2$. Let $K \subseteq F$ be finite fields and consider a Reed–Solomon code over $F$ of length $n$ and dimension $k$, with $n$ sufficiently large in terms of $\varepsilon$ and distinct evaluation points $\alpha_1, \dots, \alpha_n \in F$. Suppose $\mathrm{Gal}(F/K)$ has $g \ge 1$ generators $\sigma_1, \dots, \sigma_g$ with
--   $$
--   g \ge \frac{12\log_2(1/\varepsilon)}{\varepsilon}, \qquad |\{\alpha_i : \sigma_\ell(\alpha_i) \neq \alpha_i\}| \le \lceil n/g\rceil \text{ for every } \ell .
--   $$
--   Given the evaluation points, these generators and any received word $y \in F^n$, one can compute in time $\mathrm{poly}(n, g, \log|F|)$ a $K(X)$-basis, consisting of polynomials in $F[X]_{<k}$, of a space $A \subseteq F(X)$ with $\dim_{K(X)} A \le 2/\varepsilon$ that contains every $f \in F[X]_{<k}$ with
--   $$
--   |\{j : f(\alpha_j) = y_j\}| \ge k + \varepsilon n .
--   $$
--
--   This is the first step of the decoder of Theorem 5.1. Over $K(X)$ the candidate messages fit in a space of dimension $O(1/\varepsilon)$, independent of $n$ and $[F:K]$.
--
--   **Formalization Note** Encodings as in Theorem 5.1. $F(X)$ is a $K(X)$-vector space through the published `ratFuncAlgebra`. The output is a list of polynomials of $F[X]_{<k}$, each by its $k$ coefficients and linearly independent over $K(X)$. Its length is the dimension of its span $A$. $\mathrm{poly}(n, g, \log|F|)$ is $c(n + g + \lfloor\log_2|F|\rfloor + 2)^c$ with $c$ absolute; the machine and the threshold for $n$ depend on $\varepsilon$. "Dimension $k$" is $1 \le k \le n$.
--
--   Differences from the source:
--   - encoding: finite fields K ⊆ F; the evaluation points, the generators σ_ℓ of Gal(F/K) and y as given objects → K = 𝔽_p[Y]/(f), F = K[X]/(h) with h monic irreducible; points, y and output coefficients in the power basis of F/K; σ_ℓ input as an exponent e_ℓ < deg h with σ_ℓ(x) = x^{|K|^{e_ℓ}}; one Turing machine with an explicit step bound; reason: every finite extension is isomorphic to such a K[X]/(h) and every element of Gal(F/K) is a power of x ↦ x^{|K|}; the base mission's machine model
--   - reading: "one can compute in time poly(n, g, log|F|)" → one machine per ε, uniform over K, F, n, g, k and y, with time c(n + g + ⌊log₂|F|⌋ + 2)^c and c absolute; reason: the paper's constant convention; an algorithm per instance would empty the time clause
--   - encoding: a K(X)-basis consisting of polynomials in F[X]_{<k} of a space A with dim A ≤ 2/ε → a K(X)-linearly independent list of polynomials of F[X]_{<k} of length ≤ 2/ε whose K(X)-span contains every such f; reason: A is the span of its basis; its dimension is the length of the basis
-- source:
--   Alrabiah–Goyal–Guruswami, Explicit Reed-Solomon Subspace Designs: Optimal List and Line Decoding, arXiv:2610.36215 (held version, sha256 cf26424b…f36206), Theorem 5.2, p.23 (PDF 25)

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_RSListDecodingCapacity_AllRates_Encoding
import Definitions.Def_RSSubspaceDesign_decPoly
import Definitions.Def_RSSubspaceDesign_IsCoeffList
import Definitions.Def_RSSubspaceDesign_encField
import Definitions.Def_RSSubspaceDesign_ratFuncAlgebra

open Polynomial RSListDecodingCapacity.AllRates

namespace RSSubspaceDesign

namespace Supplement

/-- **Theorem 5.2 (Finding a low-dimensional `K(X)`-space).** Alrabiah–Goyal–Guruswami,
arXiv:2610.36215 (held version, sha256 cf26424b…f36206), Theorem 5.2, p.23.

Fix `0 < ε < 1/2`. Let `K ⊆ F` be finite fields, and consider a Reed–Solomon code of length `n` and
dimension `k` over `F`, where `n` is sufficiently large in terms of `ε`, with distinct evaluation points
`α₁, …, αₙ ∈ F`. Suppose `Gal(F/K)` has `g ≥ 1` generators `σ₁, …, σ_g` with `g ≥ 12 log₂(1/ε)/ε`,
such that for each `σ_ℓ`, `|{αᵢ | σ_ℓ(αᵢ) ≠ αᵢ}| ≤ ⌈n/g⌉`. Given the evaluation points, these
generators, and any received word `y ∈ Fⁿ`, one can compute in time `poly(n, g, log |F|)` a
`K(X)`-basis consisting of polynomials in `F[X]_{<k}` of a space `A ⊆ F(X)` with
`dim_{K(X)} A ≤ 2/ε` that contains every `f ∈ F[X]` of degree less than `k` satisfying
`|{j : f(αⱼ) = yⱼ}| ≥ k + εn`.

**Formalization Note.** Encodings as in `theorem_5_1` (`K = AdjoinRoot f`, `F = K[X]/(h)`, generators
as exponents `e_ℓ < deg h` of `x ↦ x^{|K|}`). `F(X)` is a `K(X)`-vector space through the published
`ratFuncAlgebra`; "a `K(X)`-basis of `A`" is a `K(X)`-linearly independent list of polynomials of
`F[X]_{<k}` (each written by its `k` coefficients), `A` its span, and `dim A` its length.
`poly(n, g, log|F|)` is `c(n + g + ⌊log₂|F|⌋ + 2)^c` with `c` absolute; `M` and `N` are chosen
after `ε`. "Dimension `k`" is `1 ≤ k ≤ n` (the RS code of Section 2). -/
theorem theorem_5_2 :
    ∃ c : ℕ, ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (N : ℕ),
      ∀ n : ℕ, N ≤ n →
      ∀ (p : ℕ) [Fact p.Prime] (f : (ZMod p)[X]) [Fact (Irreducible f)], f.Monic →
      ∀ hc : List (List ℕ), IsCoeffList p f ((decPoly p f hc).natDegree + 1) hc →
        (decPoly p f hc).Monic → ∀ hirr : Irreducible (decPoly p f hc),
      haveI : Fact (Irreducible (decPoly p f hc)) := ⟨hirr⟩
      ∀ ac : List (List (List ℕ)), ac.length = n →
        (∀ x ∈ ac, IsCoeffList p f (decPoly p f hc).natDegree x) →
      let α : Fin n → AdjoinRoot (decPoly p f hc) :=
        fun i => AdjoinRoot.mk (decPoly p f hc) (decPoly p f (ac.getD i []))
      Function.Injective α →
      ∀ g : ℕ, 1 ≤ g → 12 * Real.logb 2 (1 / ε) / ε ≤ g →
      ∀ e : Fin g → ℕ, (∀ l, e l < (decPoly p f hc).natDegree) →
      ∀ σ : Fin g → (AdjoinRoot (decPoly p f hc) ≃ₐ[AdjoinRoot f] AdjoinRoot (decPoly p f hc)),
        (∀ l x, σ l x = x ^ ((p ^ f.natDegree) ^ e l)) →
        Subgroup.closure (Set.range σ) = ⊤ →
        (∀ l, (Finset.univ.filter fun j => σ l (α j) ≠ α j).card ≤ ⌈(n : ℝ) / g⌉₊) →
      ∀ k : ℕ, 1 ≤ k → k ≤ n →
      ∀ yc : List (List (List ℕ)), yc.length = n →
        (∀ x ∈ yc, IsCoeffList p f (decPoly p f hc).natDegree x) →
      let y : Fin n → AdjoinRoot (decPoly p f hc) :=
        fun j => AdjoinRoot.mk (decPoly p f hc) (decPoly p f (yc.getD j []))
      let decM : List (List (List ℕ)) → (AdjoinRoot (decPoly p f hc))[X] :=
        fun m => ∑ i : Fin m.length,
          C (AdjoinRoot.mk (decPoly p f hc) (decPoly p f (m.get i))) * X ^ (i : ℕ)
      ∃ out : List (List (List (List ℕ))),
        (∀ m ∈ out, m.length = k ∧ ∀ x ∈ m, IsCoeffList p f (decPoly p f hc).natDegree x) ∧
        HMBinPacking.OutputsWithin M
          (encField p f ++ encNat n ++ encNat k ++ encList (encList encNat) hc ++
                encList (encList (encList encNat)) ac ++
            encList encNat (List.ofFn e) ++ encList (encList (encList encNat)) yc)
          (encList (encList (encList (encList encNat))) out)
          (c * (n + g + Nat.log 2 ((p ^ f.natDegree) ^ (decPoly p f hc).natDegree) + 2) ^ c) ∧
        letI := ratFuncAlgebra (AdjoinRoot f) (AdjoinRoot (decPoly p f hc))
        LinearIndependent (RatFunc (AdjoinRoot f))
          (fun i : Fin out.length =>
            algebraMap (AdjoinRoot (decPoly p f hc))[X] (RatFunc (AdjoinRoot (decPoly p f hc)))
              (decM (out.get i))) ∧
        (out.length : ℝ) ≤ 2 / ε ∧
        ∀ P ∈ degreeLT (AdjoinRoot (decPoly p f hc)) k,
          (k : ℝ) + ε * n ≤ ((Finset.univ.filter fun j => P.eval (α j) = y j).card : ℝ) →
          algebraMap (AdjoinRoot (decPoly p f hc))[X] (RatFunc (AdjoinRoot (decPoly p f hc))) P ∈
            Submodule.span (RatFunc (AdjoinRoot f))
              (Set.range fun i : Fin out.length =>
                algebraMap (AdjoinRoot (decPoly p f hc))[X] (RatFunc (AdjoinRoot (decPoly p f hc)))
                  (decM (out.get i))) := by sorry

end Supplement

end RSSubspaceDesign
