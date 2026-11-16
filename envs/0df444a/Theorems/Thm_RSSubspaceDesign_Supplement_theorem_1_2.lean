-- Prove2me | Theorems.Thm_RSSubspaceDesign_Supplement_theorem_1_2
-- name    : RSSubspaceDesign.Supplement.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T20:36:32.827247+00:00
-- url     : https://prove2.me/theorems/c19b5e71-e004-4f78-8db4-ec32217b07da
-- title:
--   Theorem 1.2 — explicit RS codes approaching the generalized Singleton bound and list-decodable to capacity in $O_\varepsilon(1)\,\mathrm{poly}(n,\log|K|)$ time
-- statement:
--   Fix $\varepsilon \in (0,1)$. For all sufficiently large $n$ and every finite field $K$ with $|K| \ge n$, one can deterministically construct, in time $|K|^{O_\varepsilon(1)}$, an extension field $F/K$ with $[F:K] = O_\varepsilon(1)$ and distinct evaluation points $A = (\alpha_1, \dots, \alpha_n) \in F^n$ such that for every $1 \le k \le n$ the Reed–Solomon code $\mathrm{RS}_F(A,k) = \{(f(\alpha_1), \dots, f(\alpha_n)) : f \in F[X]_{<k}\}$, of rate $R = k/n$, has the following two properties.
--
--   1. **Generalized Singleton bound.** For every integer list size $L \ge 1$ the code is
--   $$
--   \Bigl(\tfrac{L}{L+1}(1 - R - \varepsilon),\ L\Bigr)\text{-list-decodable}.
--   $$
--   2. **Efficient list decoding up to capacity.** A deterministic algorithm, given $y \in F^n$, outputs all codewords $c \in \mathrm{RS}_F(A,k)$ with $\Delta(c, y) \le 1 - R - \varepsilon$ in time $O_\varepsilon(1)\cdot\mathrm{poly}(n, \log|K|)$.
--
--   The radius $\frac{L}{L+1}(1-R)$ is the generalized Singleton bound, the largest radius at which any code of rate $R$ can have lists of size $L$. Property 2 reaches list-decoding capacity $1 - R$ with a deterministic polynomial-time decoder for explicit Reed–Solomon codes over extensions of an arbitrary finite field.
--
--   **Formalization Note** The model is the one of the base Theorem 1.1. $K$ is input as a prime $p$ and a monic irreducible $f \in \mathbb F_p[Y]$, so $K = \mathbb F_p[Y]/(f)$. The construction is one multi-stack Turing machine $M$ that halts within $|K|^C$ steps and outputs a monic irreducible $h \in K[X]$ of degree at most $D$ (so $F = K[X]/(h)$) and the points in the power basis of $F/K$. The decoder is one machine $M_{\mathrm{dec}}$. It reads $K$, $n$, $k$, the construction's output and $y$, and halts within $B\,(n + \lfloor\log_2|K|\rfloor + 2)^c$ steps. Its output lists every codeword in the ball once, written by its $n$ coordinates, and nothing else. The exponent $c$ is absolute. $M$, $C$, $D$, $N$, $M_{\mathrm{dec}}$ and $B$ are chosen after $\varepsilon$.
--
--   Differences from the source:
--   - reading: the theorem is labelled "informal" and has no formal restatement → stated at full strength with every quantity of the printed statement; reason: the only version in the paper; its proof (p.16) proves exactly these clauses
--   - reading: an arbitrary field K of size at least n → a finite field K with n ≤ |K|; reason: |K| enters the time bound, so K is finite
--   - encoding: a finite field K and a deterministic construction or algorithm with a running time → K = 𝔽_p[Y]/(f) input as p and a monic irreducible f; F = K[X]/(h) for a monic irreducible h; field elements by power-basis coordinates decoded structurally; one multi-stack Turing machine with an explicit step bound; reason: the base mission's published machine model; every finite field and every finite extension is isomorphic to one of these
--   - encoding: "given y ∈ Fⁿ, outputs all Reed–Solomon codewords within relative distance 1 − R − ε of y" → the decoder also reads K, n, k and the construction's output (h and the points), and outputs a repetition-free list of codewords equal to that set; reason: the algorithm acts on the constructed code, whose description is the construction's output
--   - encoding: "for every list-size L"; poly(n, log|K|); O_ε(1) → every integer L ≥ 1 (Definition 2.2); (n + ⌊log₂|K|⌋ + 2)^c with absolute c; a multiplier B chosen after ε; reason: the paper's constant conventions written out
-- source:
--   Alrabiah–Goyal–Guruswami, Explicit Reed-Solomon Subspace Designs: Optimal List and Line Decoding, arXiv:2610.36215 (held version, sha256 cf26424b…f36206), Theorem 1.2, pp.4–5 (PDF 6–7); proved p.16 (PDF 18)

import Mathlib
import Definitions.Def_Yukon_e9ee7c0e88307b8acac3260e
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_RSListDecodingCapacity_AllRates_Encoding
import Definitions.Def_RSSubspaceDesign_decPoly
import Definitions.Def_RSSubspaceDesign_IsCoeffList
import Definitions.Def_RSSubspaceDesign_encField
import Definitions.Def_RSSubspaceDesign_Supplement_IsListDecodable

open Polynomial RSListDecodingCapacity.AllRates

namespace RSSubspaceDesign

namespace Supplement

/-- **Theorem 1.2 (Explicit RS codes approaching GSB and efficiently list-decodable up to capacity
(informal)).** Alrabiah–Goyal–Guruswami, arXiv:2610.36215 (held version, sha256 cf26424b…f36206),
Theorem 1.2, pp.4–5 (proved p.16, in the proof of Theorem 1.1).

Fix `ε ∈ (0, 1)`. For all sufficiently large `n`, and an arbitrary field `K` of size at least `n`,
one can deterministically construct in time `|K|^{O_ε(1)}` an extension field `F` over `K` with
`[F : K] = O_ε(1)` and evaluation points `A = (α₁, …, αₙ) ∈ Fⁿ`, such that for every `1 ≤ k ≤ n` the
Reed–Solomon code `RS_F(A, k)` of rate `R = k/n` has the following properties:
(a) (Generalized Singleton bound.) For every list-size `L`, it is
`(L/(L+1) (1 − R − ε), L)`-list-decodable.
(b) (Efficient list decoding up to capacity.) There is a deterministic algorithm that, given
`y ∈ Fⁿ`, outputs all Reed–Solomon codewords within relative distance `1 − R − ε` of `y` in time
`O_ε(1) poly(n, log |K|)`.

**Formalization Note.** Construction model and encodings as in the base Theorem 1.1 (`K` as
`p, f`; output `h` and the points in the power basis of `F = K[X]/(h)`, decoded structurally); `K`
is finite (its size enters the time bound). The construction machine `M`, its exponent `C`, the
degree bound `D`, the threshold `N`, the decoder `M_dec` and its multiplier `B` are chosen after
`ε`; the exponent `c` of `poly` is absolute, chosen first: `poly(n, log|K|)` is
`(n + ⌊log₂|K|⌋ + 2)^c`. The decoder reads `K`, `n`, `k`, the construction's output (`h`, the
points) and `y` (its `n` coordinate lists); it outputs a list of codewords, each as `n` coordinate
lists, without repetition and exactly the codewords `c ∈ RS_F(A, k)` with `Δ(c, y) ≤ 1 − k/n − ε`.
"Every list-size `L`" is every integer `L ≥ 1` (Definition 2.2). List decodability is Definition 2.2
(`IsListDecodable`, closed ball `Δ(c, y) ≤ δ`, at most `L` codewords). -/
theorem theorem_1_2 :
    ∃ c : ℕ, ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ (M Mdec : Turing.TM2ComputableAux Bool Bool) (N D C B : ℕ),
        ∀ n : ℕ, N ≤ n →
        ∀ (p : ℕ) [Fact p.Prime] (f : (ZMod p)[X]) [Fact (Irreducible f)], f.Monic →
          n ≤ p ^ f.natDegree →
          ∃ (hc : List (List ℕ)) (ac : List (List (List ℕ))),
            IsCoeffList p f ((decPoly p f hc).natDegree + 1) hc ∧
            ac.length = n ∧ (∀ x ∈ ac, IsCoeffList p f (decPoly p f hc).natDegree x) ∧
            HMBinPacking.OutputsWithin M (encField p f ++ encNat n)
              (encList (encList encNat) hc ++ encList (encList (encList encNat)) ac)
              ((p ^ f.natDegree) ^ C) ∧
            (decPoly p f hc).Monic ∧ (decPoly p f hc).natDegree ≤ D ∧
            ∃ hirr : Irreducible (decPoly p f hc),
            haveI : Fact (Irreducible (decPoly p f hc)) := ⟨hirr⟩
            ∃ hα : Function.Injective fun i : Fin n =>
                AdjoinRoot.mk (decPoly p f hc) (decPoly p f (ac.getD i [])),
              ∀ k : ℕ, 1 ≤ k → k ≤ n →
                (∀ L : ℕ, 1 ≤ L →
                  IsListDecodable (ReedSolomon.code ⟨_, hα⟩ k : Set (Fin n → AdjoinRoot (decPoly p f hc)))
                    ((L : ℝ) / (L + 1) * (1 - (k : ℝ) / n - ε)) L) ∧
                ∀ yc : List (List (List ℕ)), yc.length = n →
                  (∀ x ∈ yc, IsCoeffList p f (decPoly p f hc).natDegree x) →
                  ∃ out : List (List (List (List ℕ))),
                    (∀ w ∈ out, w.length = n ∧
                      ∀ x ∈ w, IsCoeffList p f (decPoly p f hc).natDegree x) ∧
                    HMBinPacking.OutputsWithin Mdec
                      (encField p f ++ encNat n ++ encNat k ++ encList (encList encNat) hc ++
                        encList (encList (encList encNat)) ac ++
                        encList (encList (encList encNat)) yc)
                      (encList (encList (encList (encList encNat))) out)
                      (B * (n + Nat.log 2 (p ^ f.natDegree) + 2) ^ c) ∧
                    let dec : List (List (List ℕ)) → Fin n → AdjoinRoot (decPoly p f hc) :=
                      fun w i => AdjoinRoot.mk (decPoly p f hc) (decPoly p f (w.getD i []));
                    (out.map dec).Nodup ∧
                    ∀ w : Fin n → AdjoinRoot (decPoly p f hc),
                      w ∈ out.map dec ↔
                        (w ∈ ReedSolomon.code ⟨_, hα⟩ k ∧
                          relDist w (dec yc) ≤ 1 - (k : ℝ) / n - ε) := by sorry

end Supplement

end RSSubspaceDesign
