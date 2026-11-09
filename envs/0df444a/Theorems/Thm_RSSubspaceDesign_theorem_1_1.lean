-- Prove2me | Theorems.Thm_RSSubspaceDesign_theorem_1_1
-- name    : RSSubspaceDesign.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:28:29.816898+00:00
-- url     : https://prove2.me/theorems/1a088f94-38c8-4061-bba5-a390c8035167
-- title:
--   Theorem 1.1 — explicit Reed–Solomon codes built in $|K|^{O_{r,\varepsilon}(1)}$ time that are $\tau$-subspace designs with $\tau(d)=\min\{1,R+\varepsilon/4\}$ ($d\le r$) over every subfield
-- statement:
--   For every integer $r\ge2$, every $0<\varepsilon<1$, all sufficiently large $n$, and every finite field $K$ with $|K|\ge n$, one can deterministically construct in time $|K|^{O_{r,\varepsilon}(1)}$ an extension $F/K$ of degree $O_{r,\varepsilon}(1)$ and evaluation points $A=(\alpha_1,\dots,\alpha_n)\in F^n$ with the following property. For every $1\le k\le n$, the Reed–Solomon code $C=\mathrm{RS}_F(A,k)$, of rate $R=k/n$, is a $\tau$-subspace-design code over every subfield $K_0\subseteq K$, where
--   $$\tau(d)=\min\{1,\,R+\varepsilon/4\}\quad(1\le d\le r),\qquad \tau(d)=1\quad(d>r).$$
--
--   By the results of Chen–Zhang and Brakensiek–Chen–Dhar–Zhang, such codes are list-decodable approaching the generalized Singleton bound and list-recoverable near capacity; this is the first explicit construction of Reed–Solomon evaluation points with this guarantee.
--
--   **Formalization Note** One Turing machine per $(r,\varepsilon)$, with threshold $N$, degree bound $D$ and time exponent $C$ fixed before $n$ and $K$. The input is $(p,f,n)$ with $K=\mathbb F_p[Y]/(f)$; the output is $F=K[X]/(h)$ ($h$ monic irreducible of degree $\le D$) and the $n$ distinct points in the power basis of $F/K$, produced within $|K|^{C}$ steps.
--
--   Differences from the source:
--   - encoding: every finite field K → K = 𝔽_p[Y]/(f) for a prime p and a monic irreducible f ∈ 𝔽_p[Y], input as (p, f); reason: every finite field is isomorphic to one of these and the statement is invariant under isomorphism
--   - encoding: one can deterministically construct in time |K|^{O_{r,ε}(1)} an extension F/K of degree O_{r,ε}(1) and points A ∈ Fⁿ → one multi-stack Turing machine per (r, ε) that, on input (p, f, n), halts within |K|^C steps with F = K[X]/(h) (coefficient lists of a monic irreducible h with deg h ≤ D) and the n distinct points in the power basis of F/K; N, D, C chosen with the machine, before n and K; reason: the paper fixes no machine model; Turing machines simulate any reasonable deterministic model with polynomial overhead, absorbed by |K|^{O(1)}, and every reasonable representation of F and its elements converts to this one in poly(|F|) time
--   - encoding: every subfield K₀ ⊆ K → every field K₀ with an algebra K₀ → K, F a K₀-algebra through K, the code viewed over K₀ by restrictScalars; reason: a field homomorphism is injective, so this identifies K₀ with a subfield of K; every subfield is the case of its inclusion; same instances up to isomorphism
--   - encoding: τ-subspace-design code (Definition 2.1, τ nondecreasing with values in [0, 1]); τ on ℤ≥1; R = k/n → IsSubspaceDesign with no precondition on τ; τ on ℕ (value at 0 unused); k/n written out; reason: the stated τ is nondecreasing with values in [0, 1] on d ≥ 1 (checked), so the claim is the same
-- source:
--   O. Alrabiah, R. Goyal, V. Guruswami, Explicit Reed-Solomon Subspace Designs: Optimal List and Line Decoding, arXiv:2610.36215 (held version, sha256 cf26424b…), Theorem 1.1, p.4 (PDF p.6); restated p.15 (PDF p.17)

import Mathlib
import Definitions.Def_Yukon_e9ee7c0e88307b8acac3260e
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_RSListDecodingCapacity_AllRates_Encoding
import Definitions.Def_RSSubspaceDesign_IsSubspaceDesign
import Definitions.Def_RSSubspaceDesign_decPoly
import Definitions.Def_RSSubspaceDesign_IsCoeffList
import Definitions.Def_RSSubspaceDesign_encField

open Polynomial RSListDecodingCapacity.AllRates

namespace RSSubspaceDesign

/-- **Theorem 1.1 (Explicit RS codes that are near-optimal subspace-design codes).**
Alrabiah–Goyal–Guruswami, *Explicit Reed-Solomon Subspace Designs: Optimal List and Line
Decoding*, arXiv:2610.36215 (held version, sha256 cf26424b…f36206), Theorem 1.1, p.4 (restated
p.15).

For every integer `r ≥ 2`, every `0 < ε < 1`, all sufficiently large `n`, and every finite field
`K` with `|K| ≥ n`, one can deterministically construct in time `|K|^{O_{r,ε}(1)}` an extension
`F/K` of degree `O_{r,ε}(1)` and evaluation points `A = (α₁, …, αₙ) ∈ Fⁿ` such that for every
`1 ≤ k ≤ n` the Reed–Solomon code `C = RS_F(A, k)`, of rate `R = k/n`, is a `τ`-subspace-design code
over every subfield `K₀ ⊆ K`, where `τ(d) = min{1, R + ε/4}` for `1 ≤ d ≤ r` and `τ(d) = 1` for
`d > r`.

**Formalization Note.** `K` is input as a prime `p` and a monic irreducible `f ∈ 𝔽_p[Y]`
(`K = AdjoinRoot f`, `|K| = p^{deg f}`), followed by `n`; every finite field is isomorphic to one
of these. "Deterministically construct in time `|K|^{O_{r,ε}(1)}`" is one multi-stack Turing machine
`M` per `(r, ε)` that halts within `|K|^C` steps with the output; the threshold `N`, the degree bound
`D` and the exponent `C` are chosen with `M`, before `n` and `K`. The output is `F = K[X]/(h)` as
the coefficient lists of a monic irreducible `h` of degree `≤ D` (`[F : K] = deg h`), and the `n`
points in the power basis of `F/K` (`decPoly`, `IsCoeffList`; decoding by `AdjoinRoot.mk`); the
points are distinct. `RS_F(A, k)` is the public `ReedSolomon.code`. "Every subfield `K₀ ⊆ K`" is
every field `K₀` with an algebra `K₀ → K`; `F = AdjoinRoot h` is then a `K₀`-algebra through `K`
(Mathlib's `AdjoinRoot` instance), and the code is viewed over `K₀` by `restrictScalars`. `τ` is
given on all of `ℕ` (its value at `0` is unused) with `R = k/n` written out. -/
theorem theorem_1_1 :
    ∀ r : ℕ, 2 ≤ r → ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ (M : Turing.TM2ComputableAux Bool Bool) (N D C : ℕ),
        ∀ n : ℕ, N ≤ n →
        ∀ (p : ℕ) [Fact p.Prime] (f : (ZMod p)[X]) [Fact (Irreducible f)], f.Monic →
          n ≤ p ^ f.natDegree →
          ∃ (hc : List (List ℕ)) (ac : List (List (List ℕ))),
            IsCoeffList p f ((decPoly p f hc).natDegree + 1) hc ∧
            ac.length = n ∧ (∀ x ∈ ac, IsCoeffList p f (decPoly p f hc).natDegree x) ∧
            HMBinPacking.OutputsWithin M (encField p f ++ encNat n)
              (encList (encList encNat) hc ++ encList (encList (encList encNat)) ac)
              ((p ^ f.natDegree) ^ C) ∧
            (decPoly p f hc).Monic ∧ Irreducible (decPoly p f hc) ∧
            (decPoly p f hc).natDegree ≤ D ∧
            ∃ hα : Function.Injective fun i : Fin n =>
                AdjoinRoot.mk (decPoly p f hc) (decPoly p f (ac.getD i [])),
              ∀ k : ℕ, 1 ≤ k → k ≤ n →
              ∀ (K₀ : Type) [Field K₀] [Algebra K₀ (AdjoinRoot f)],
                IsSubspaceDesign K₀ ((ReedSolomon.code ⟨_, hα⟩ k).restrictScalars K₀)
                  fun d => if d ≤ r then min 1 ((k : ℝ) / n + ε / 4) else 1 := by sorry

end RSSubspaceDesign
