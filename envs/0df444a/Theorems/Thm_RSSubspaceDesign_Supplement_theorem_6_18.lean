-- Prove2me | Theorems.Thm_RSSubspaceDesign_Supplement_theorem_6_18
-- name    : RSSubspaceDesign.Supplement.theorem_6_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T20:43:30.569224+00:00
-- url     : https://prove2.me/theorems/34bcd9a2-4e23-4275-8acf-b454dc8e3d96
-- title:
--   Theorem 6.18 — from a prepared relation space, compute a new relation vanishing on $Z(R)$ or a branching form $\ell$, in time $O_{d,\varepsilon}(1)\,\mathrm{poly}(n,\log|F|)$
-- statement:
--   Work in the setting of Section 6.2 (the pruning step of Theorem 5.3). Let $d \ge 1$, $0 < \varepsilon < 1/2$, $t = \lfloor 16d/\varepsilon \rfloor$, $M_s = \{Z^a : \mathrm{wt}(a) \le s\}$, $L = K(X)$, $S_s = \mathrm{span}_L M_s \subseteq L[Z_1,\dots,Z_d]$ and $B(d,t) = |M_t|\,t$. Let $K \subseteq F$ be finite fields, $n$ sufficiently large in terms of $d, \varepsilon$, and $\alpha_1,\dots,\alpha_n \in F$ pairwise nonconjugate over $K$ with $\delta_j = [K(\alpha_j):K]$, $\delta_{\min} \ge C(d,\varepsilon)$ where $C(d,\varepsilon)$ satisfies (6.2) and (6.4), and $\delta_{\max} \le 2\delta_{\min}$. Let $y \in F^n$, $1 \le k \le n$, and $f_1,\dots,f_d \in F[X]_{<k}$. Order $M_t$ by decreasing total degree with an arbitrary tie-break. Let $R \subseteq S_t$ be stored by a row-echelon basis with entries in $K[X]$ (Definition 6.10); let $P_s$ be the remaining (non-pivot) monomials of degree $\le s$, $W_s = \mathrm{span}_L P_s$; let $R(\alpha_j)$ be the $K(\alpha_j)$-span of the stored rows evaluated at $X = \alpha_j$, $W_s(\alpha_j) = \mathrm{span}_{K(\alpha_j)} P_s$, $B$ the set of coordinates where some pivot entry vanishes, $L_j$ the $K(\alpha_j)$-span of the expansion of $\sum_i f_i(\alpha_j) Z_i - y_j$ in a basis of $F$ over $K(\alpha_j)$, $J = \{j : L_j \not\subseteq R(\alpha_j)\}$, and, for $j \in J \setminus B$, any $\ell_j \in L_j \setminus R(\alpha_j)$ and $a_j = \dim_{K(\alpha_j)}(\ell_j W_{t-1}(\alpha_j) \cap R(\alpha_j))$.
--
--   Suppose $R \subsetneq S_t$ is $B(d,t)k$-prepared (ready, Definition 6.3, with stored entries of degree $\le B(d,t)k$) and
--   $$
--   \sum_{j \in J \setminus B} a_j \ \ge\ \frac{\varepsilon n}{8}\,|P_t| .
--   $$
--   Then one can compute, in time $O_{d,\varepsilon}(1)\,\mathrm{poly}(n, \log|F|)$, one of the following:
--   - a relation $Q \in S_t \setminus R$ vanishing on $Z(R)$ (the common zeros of $R$ in $L^d$);
--   - an affine linear form $\ell \in S_1 \setminus R$ over $L$ with $\dim_L(\ell W_{t-1} \cap R) \ge \frac{\varepsilon}{16}|P_t|$.
--
--   **Formalization Note** Encodings as in Theorem 5.3 ($K = \mathbb F_p[Y]/(f)$, $F = K[X]/(h)$, power-basis coordinates, one Turing machine per $(d,\varepsilon)$ with an explicit step bound $B\,(n + \lfloor\log_2|F|\rfloor + 2)^c$, $c$ absolute, $B$ after $d,\varepsilon$). The monomial order is an input list enumerating $M_t$ without repetition by nonincreasing total degree; the stored matrix is a list of nonzero rows with pairwise distinct pivots (first monomial in the order with a nonzero entry), each entry of $K[X]$ by exactly $B(d,t)k+1$ coefficients. $L_j$ is the set of images of the form under all $K(\alpha_j)$-linear maps $F \to K(\alpha_j)$ applied to the coefficients, which is the span of its expansion in a basis. The output is a tag ($0$ for $Q$, $1$ for $\ell$) and the polynomial over $L$ as terms (monomial, numerator, denominator in $K[X]$).
--
--   Differences from the source:
--   - encoding: K ⊆ F finite fields, the points, y, the f_i, the monomial order and the stored matrix of R as given objects; "we can compute" → K = 𝔽_p[Y]/(f) and F = K[X]/(h) input by coefficients; elements in the power basis; the order of M_t as an input list; the stored matrix as a list of rows of (monomial, K[X]-entry) terms with entries of exactly B(d,t)k + 1 coefficients; the output as a tag and a list of (monomial, numerator, denominator) terms; one Turing machine with an explicit step bound; reason: the base mission's machine model; every finite field and finite extension is isomorphic to these; the fixed entry length is the degree bound of B(d,t)k-prepared
--   - encoding: a row-echelon basis over L with denominators cleared (Definition 6.10) → nonzero rows with entries in K[X] whose pivots (first monomial in the order with a nonzero entry) are pairwise distinct; R their L-span; reason: a list of rows with distinct pivots is a row-echelon matrix up to the order of its rows, which no object of the theorem depends on
--   - reading: "then we can compute one of the following" (no time bound in the statement) → computable in time O_{d,ε}(1) poly(n, log|F|), poly with an absolute exponent; reason: the bound the proof proves for this step (p.38, PDF 40: "the algorithm can be implemented in time O_{d,ε}(1) poly(n, log|F|)"), the house convention for poly
--   - reading: arbitrary tie-breaking of the monomial order; "choose any ℓ_j ∈ L_j \ R(α_j)" → quantified universally (the order is an input, the conclusion holds for every choice of the ℓ_j satisfying the hypothesis); reason: the page leaves both choices arbitrary; the universal reading is the stronger one and the proof uses no property of the choice
--   - generalization: δ_min ≥ C(d, ε) with C(d, ε) chosen large enough for (6.2) and (6.4) → δ_j ≥ 16|M_t|²t/ε and δ_j ≥ (32|M_t|B(d,t)/ε)(1 + (d+1)|M_t|V), V = binom(d + 2(3|M_t|)^d, d), for every j; reason: these are the only properties of C(d, ε) the proof uses; every admissible C(d, ε) satisfies them, so the statement specializes to the paper's
--   - generalization: f_1, …, f_d a reduced K[X]-basis of A ∩ F[X] (Lemma 6.9) → any f_1, …, f_d ∈ F[X]_{<k}; reason: the proof of Theorem 6.18 uses the f_i only through L_j and J; a reduced basis has degree < k (Lemma 6.9), so the paper's f_i are an instance
-- source:
--   Alrabiah–Goyal–Guruswami, Explicit Reed-Solomon Subspace Designs: Optimal List and Line Decoding, arXiv:2610.36215 (held version, sha256 cf26424b…f36206), Theorem 6.18, p.36 (PDF 38); setting of Section 6.2, pp.32–36 (PDF 34–38), and Section 6.1, p.27 (PDF 29)

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_RSListDecodingCapacity_AllRates_Encoding
import Definitions.Def_RSSubspaceDesign_decPoly
import Definitions.Def_RSSubspaceDesign_IsCoeffList
import Definitions.Def_RSSubspaceDesign_encField

open Polynomial RSListDecodingCapacity.AllRates

namespace RSSubspaceDesign

namespace Supplement

open Classical in
/-- **Theorem 6.18 (Finding a relation or a branching form).** Alrabiah–Goyal–Guruswami,
arXiv:2610.36215 (held version, sha256 cf26424b…f36206), Theorem 6.18, p.36 (PDF 38), in the
setting of Section 6.2, pp.32–36 (PDF 34–38), with the notation of Section 6.1, p.27 (PDF 29),
and the standing hypotheses of Theorem 5.3, p.25 (PDF 27).

Setting: `K ⊆ F` finite fields, `L = K(X)`, pairwise nonconjugate `α₁, …, αₙ ∈ F` with
`δⱼ = [K(αⱼ) : K]`, `δ_min ≥ C(d, ε)` where `C(d, ε)` satisfies (6.2) and (6.4), `δ_max ≤ 2δ_min`,
`y ∈ Fⁿ`, `1 ≤ k ≤ n` with `n` sufficiently large in `d, ε`, polynomials `f₁, …, f_d`,
`t = ⌊16d/ε⌋`, `M_s = {Z^a : wt(a) ≤ s}`, `S_s = span_L M_s`, `B(d, t) = |M_t| t`. The monomials of
`M_t` are ordered by decreasing total degree with arbitrary tie-breaking; `R ⊆ S_t` is stored by a
row-echelon basis with entries in `K[X]` (Definition 6.10); pivots, `P_s`, `W_s`; ready
(Definition 6.3); `R(αⱼ)`, `W_s(αⱼ)`, the exceptional set `B`, `Lⱼ` and `J` (Definition 6.14); at
regular undetermined `j`, any `ℓⱼ ∈ Lⱼ ∖ R(αⱼ)` and `aⱼ = dim_{K(αⱼ)}(ℓⱼ W_{t−1}(αⱼ) ∩ R(αⱼ))`.

Suppose `R ⊊ S_t` is `B(d, t)k`-prepared and `∑_{j ∈ J∖B} aⱼ ≥ (εn/8)|P_t|`. Then we can compute
one of the following: a relation `Q ∈ S_t ∖ R` vanishing on `Z(R)`; or an affine linear form
`ℓ ∈ S_1 ∖ R`, over `L`, such that `dim_L(ℓ W_{t−1} ∩ R) ≥ (ε/16)|P_t|`.

**Formalization Note.** Encodings as in `theorem_5_3`: `K = AdjoinRoot f` (input `p, f`),
`F = K[X]/(h)` (input `h`'s coefficients `hc`), points and `y` in the power basis of `F/K`, each
`fᵢ` by `k` coefficients in `F` (degree `< k`, as for the reduced basis of Lemma 6.9). A monomial
`Z^a` is its exponent list `a` (length `d`, 0-based variables). The order of `M_t` is an input list
`oc` enumerating `M_t` without repetition with nonincreasing total degree (every tie-break is
allowed). The stored matrix is a list `rc` of rows; a row is a list of terms (monomial, entry in
`K[X]` by exactly `B(d, t)k + 1` coefficients, so its degree is `≤ B(d, t)k`), with distinct
monomials of degree `≤ t`; "row-echelon" is: every row is nonzero and the rows have pairwise
distinct pivots, the pivot of a row being its first monomial in the order with a nonzero entry
(the order of the rows is immaterial). `R` is the `L`-span of the rows. `R(αⱼ)` is the
`K(αⱼ)`-span of the rows with every entry evaluated at `X = αⱼ`, inside `F[Z]`; `W_s(αⱼ)` is the
`K(αⱼ)`-span of `P_s`; `Lⱼ` is the set of images of `∑ᵢ fᵢ(αⱼ)Zᵢ − yⱼ` under all `K(αⱼ)`-linear
maps `F → K(αⱼ)` applied to the coefficients (equal to the span of its expansion in a basis of
`F` over `K(αⱼ)`). `C(d, ε)` is replaced by its two defining lower bounds (6.2)
`C ≥ 16|M_t|²t/ε` and (6.4) `C ≥ (32|M_t|B(d, t)/ε)(1 + (d + 1)|M_t|V)`,
`V = binom(d + 2(3|M_t|)^d, d)`. The choices `ℓⱼ` are quantified universally. "We can compute" is
one machine per `(d, ε)` with the bound the proof gives (p.38, PDF 40):
`O_{d,ε}(1) · poly(n, log |F|)`, the exponent `c` absolute, the multiplier `B` chosen after
`d, ε`. The output is a tag (`0`: a relation `Q`, `1`: a branching form `ℓ`) and the polynomial
over `L` as a list of terms (monomial, numerator, denominator in `K[X]`). -/
theorem theorem_6_18 :
    ∃ c : ℕ, ∀ d : ℕ, 1 ≤ d → ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (N B : ℕ),
      ∀ n : ℕ, N ≤ n →
      ∀ (p : ℕ) [Fact p.Prime] (f : (ZMod p)[X]) [Fact (Irreducible f)], f.Monic →
      ∀ hc : List (List ℕ), IsCoeffList p f ((decPoly p f hc).natDegree + 1) hc →
        (decPoly p f hc).Monic → ∀ hirr : Irreducible (decPoly p f hc),
      haveI : Fact (Irreducible (decPoly p f hc)) := ⟨hirr⟩
      let t : ℕ := ⌊16 * (d : ℝ) / ε⌋₊
      let Mt : ℕ := (d + t).choose d
      let Bdt : ℕ := Mt * t
      let V : ℕ := (d + 2 * (3 * Mt) ^ d).choose d
      ∀ ac : List (List (List ℕ)), ac.length = n →
        (∀ x ∈ ac, IsCoeffList p f (decPoly p f hc).natDegree x) →
      let α : Fin n → AdjoinRoot (decPoly p f hc) :=
        fun i => AdjoinRoot.mk (decPoly p f hc) (decPoly p f (ac.getD i []))
      let δ : Fin n → ℕ := fun j => (minpoly (AdjoinRoot f) (α j)).natDegree
      (∀ i j : Fin n, i ≠ j → ∀ τ : AdjoinRoot (decPoly p f hc) ≃ₐ[AdjoinRoot f]
          AdjoinRoot (decPoly p f hc), τ (α i) ≠ α j) →
      (∀ j : Fin n, 16 * (Mt : ℝ) ^ 2 * t / ε ≤ δ j) →
      (∀ j : Fin n, 32 * (Mt : ℝ) * Bdt / ε * (1 + (d + 1) * Mt * V) ≤ δ j) →
      (∀ i j : Fin n, δ i ≤ 2 * δ j) →
      ∀ k : ℕ, 1 ≤ k → k ≤ n →
      ∀ yc : List (List (List ℕ)), yc.length = n →
        (∀ x ∈ yc, IsCoeffList p f (decPoly p f hc).natDegree x) →
      let y : Fin n → AdjoinRoot (decPoly p f hc) :=
        fun j => AdjoinRoot.mk (decPoly p f hc) (decPoly p f (yc.getD j []))
      let decM : List (List (List ℕ)) → (AdjoinRoot (decPoly p f hc))[X] :=
        fun m => ∑ i : Fin m.length,
          C (AdjoinRoot.mk (decPoly p f hc) (decPoly p f (m.get i))) * X ^ (i : ℕ)
      ∀ fc : List (List (List (List ℕ))), fc.length = d →
        (∀ b ∈ fc, b.length = k ∧ ∀ x ∈ b, IsCoeffList p f (decPoly p f hc).natDegree x) →
      let fpol : Fin d → (AdjoinRoot (decPoly p f hc))[X] := fun i => decM (fc.getD i [])
      let mono : List ℕ → (Fin d →₀ ℕ) := fun e => Finsupp.equivFunOnFinite.symm fun i => e.getD i 0
      ∀ oc : List (List ℕ),
        (∀ e ∈ oc, e.length = d) → (oc.map mono).Nodup →
        (∀ m : Fin d →₀ ℕ, m ∈ oc.map mono ↔ m.degree ≤ t) →
        (oc.map mono).Pairwise (fun a b => b.degree ≤ a.degree) →
      ∀ rc : List (List (List ℕ × List (List ℕ))),
        (∀ row ∈ rc, (row.map fun u => mono u.1).Nodup ∧
          ∀ u ∈ row, u.1.length = d ∧ (mono u.1).degree ≤ t ∧
            IsCoeffList p f (Bdt * k + 1) u.2) →
      let rows : List (MvPolynomial (Fin d) (AdjoinRoot f)[X]) :=
        rc.map fun row => (row.map fun u => MvPolynomial.monomial (mono u.1) (decPoly p f u.2)).sum
      let lead : MvPolynomial (Fin d) (AdjoinRoot f)[X] → Option (Fin d →₀ ℕ) :=
        fun r => (oc.map mono).find? fun m => r.coeff m ≠ 0
      (∀ r ∈ rows, r ≠ 0) → (rows.map lead).Nodup →
      let toL : MvPolynomial (Fin d) (AdjoinRoot f)[X] → MvPolynomial (Fin d) (RatFunc (AdjoinRoot f)) :=
        MvPolynomial.map (algebraMap (AdjoinRoot f)[X] (RatFunc (AdjoinRoot f)))
      let R : Submodule (RatFunc (AdjoinRoot f)) (MvPolynomial (Fin d) (RatFunc (AdjoinRoot f))) :=
        Submodule.span (RatFunc (AdjoinRoot f)) {q | q ∈ rows.map toL}
      let S : ℕ → Submodule (RatFunc (AdjoinRoot f)) (MvPolynomial (Fin d) (RatFunc (AdjoinRoot f))) :=
        fun s => MvPolynomial.restrictTotalDegree (Fin d) (RatFunc (AdjoinRoot f)) s
      R < S t →
      (∀ r ∈ R, r ∈ S (t - 1) → ∀ a : Fin d, MvPolynomial.X a * r ∈ R) →
      let P : ℕ → Finset (Fin d →₀ ℕ) := fun s =>
        (oc.map mono).toFinset.filter fun m => some m ∉ rows.map lead ∧ m.degree ≤ s
      let evR : Fin n → MvPolynomial (Fin d) (AdjoinRoot f)[X] →
          MvPolynomial (Fin d) (AdjoinRoot (decPoly p f hc)) :=
        fun j => MvPolynomial.map (Polynomial.aeval (α j)).toRingHom
      let Kα : Fin n → IntermediateField (AdjoinRoot f) (AdjoinRoot (decPoly p f hc)) :=
        fun j => IntermediateField.adjoin (AdjoinRoot f) {α j}
      let Rα : (j : Fin n) → Submodule (Kα j) (MvPolynomial (Fin d) (AdjoinRoot (decPoly p f hc))) :=
        fun j => Submodule.span (Kα j) {q | q ∈ rows.map (evR j)}
      let Wα : (j : Fin n) → ℕ → Submodule (Kα j) (MvPolynomial (Fin d) (AdjoinRoot (decPoly p f hc))) :=
        fun j s => Submodule.span (Kα j)
          ((fun m => MvPolynomial.monomial m (1 : AdjoinRoot (decPoly p f hc))) '' ↑(P s))
      let Bset : Finset (Fin n) := Finset.univ.filter fun j =>
        ∃ r ∈ rows, ∃ m, lead r = some m ∧ Polynomial.aeval (α j) (r.coeff m) = 0
      let form : Fin n → MvPolynomial (Fin d) (AdjoinRoot (decPoly p f hc)) := fun j =>
        (∑ i : Fin d, MvPolynomial.C ((fpol i).eval (α j)) * MvPolynomial.X i) - MvPolynomial.C (y j)
      let Lset : (j : Fin n) → Set (MvPolynomial (Fin d) (AdjoinRoot (decPoly p f hc))) := fun j =>
        {q | ∃ φ : AdjoinRoot (decPoly p f hc) →ₗ[Kα j] Kα j,
          ∀ m, q.coeff m = ((φ ((form j).coeff m) : Kα j) : AdjoinRoot (decPoly p f hc))}
      let Jset : Finset (Fin n) := Finset.univ.filter fun j => ¬ Lset j ⊆ Rα j
      ∀ ℓsel : Fin n → MvPolynomial (Fin d) (AdjoinRoot (decPoly p f hc)),
        (∀ j ∈ Jset \ Bset, ℓsel j ∈ Lset j ∧ ℓsel j ∉ Rα j) →
        ε * n / 8 * (P t).card ≤
          ∑ j ∈ Jset \ Bset, (Module.finrank (Kα j)
            ↥(Submodule.map (LinearMap.mulLeft (Kα j) (ℓsel j)) (Wα j (t - 1)) ⊓ Rα j) : ℝ) →
      ∃ (tag : ℕ) (qc : List (List ℕ × List (List ℕ) × List (List ℕ))),
        HMBinPacking.OutputsWithin M
          (encField p f ++ encNat n ++ encNat k ++ encList (encList encNat) hc ++
            encList (encList (encList encNat)) ac ++ encList (encList (encList encNat)) yc ++
            encList (encList (encList (encList encNat))) fc ++ encList (encList encNat) oc ++
            encList (encList fun u : List ℕ × List (List ℕ) =>
              encList encNat u.1 ++ encList (encList encNat) u.2) rc)
          (encNat tag ++ encList (fun u : List ℕ × List (List ℕ) × List (List ℕ) =>
              encList encNat u.1 ++ encList (encList encNat) u.2.1 ++
                encList (encList encNat) u.2.2) qc)
          (B * (n + Nat.log 2 ((p ^ f.natDegree) ^ (decPoly p f hc).natDegree) + 2) ^ c) ∧
        let Q : MvPolynomial (Fin d) (RatFunc (AdjoinRoot f)) :=
          (qc.map fun u => MvPolynomial.monomial (mono u.1)
            (algebraMap (AdjoinRoot f)[X] (RatFunc (AdjoinRoot f)) (decPoly p f u.2.1) /
              algebraMap (AdjoinRoot f)[X] (RatFunc (AdjoinRoot f)) (decPoly p f u.2.2))).sum
        let WL : Submodule (RatFunc (AdjoinRoot f)) (MvPolynomial (Fin d) (RatFunc (AdjoinRoot f))) :=
          Submodule.span (RatFunc (AdjoinRoot f))
            ((fun m => MvPolynomial.monomial m (1 : RatFunc (AdjoinRoot f))) '' ↑(P (t - 1)))
        (tag = 0 ∧ Q ∈ S t ∧ Q ∉ R ∧
            ∀ z : Fin d → RatFunc (AdjoinRoot f), (∀ r ∈ R, MvPolynomial.eval z r = 0) →
              MvPolynomial.eval z Q = 0) ∨
          (tag = 1 ∧ Q ∈ S 1 ∧ Q ∉ R ∧
            ε / 16 * (P t).card ≤
              (Module.finrank (RatFunc (AdjoinRoot f))
                ↥(Submodule.map (LinearMap.mulLeft (RatFunc (AdjoinRoot f)) Q) WL ⊓ R) : ℝ)) := by sorry

end Supplement

end RSSubspaceDesign
