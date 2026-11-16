-- Prove2me | Theorems.Thm_RSSubspaceDesign_Supplement_theorem_1_3
-- name    : RSSubspaceDesign.Supplement.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T20:37:22.598479+00:00
-- url     : https://prove2.me/theorems/2ef13042-50f7-4c93-8636-aa2553c111fd
-- title:
--   Theorem 1.3 — strongly explicit RS codes, $(1-R-\varepsilon, (1/\varepsilon)^{O(1/\varepsilon)})$-list-decodable in $O_\varepsilon(1)\,\mathrm{poly}(n,\log|F|)$ time
-- statement:
--   Fix $\varepsilon \in (0,1)$. For all sufficiently large $n$ and every finite field $K$ with $|K| \ge n$, there is a strongly explicit construction of an extension field $F/K$ with $[F:K] = O_\varepsilon(1)$ and distinct evaluation points $A = (\alpha_1, \dots, \alpha_n) \in F^n$ with three properties:
--
--   1. given an index $i \in [n]$, the point $\alpha_i$ (and the description of $F$) can be computed in time $\mathrm{poly}(\log|F|)$;
--   2. for every $1 \le k \le n$ the code $\mathrm{RS}_F(A, k)$, of rate $R = k/n$, is
--   $$
--   \bigl(1 - R - \varepsilon,\ (1/\varepsilon)^{O(1/\varepsilon)}\bigr)\text{-list-decodable};
--   $$
--   3. the list can be found deterministically in time $O_\varepsilon(1)\cdot\mathrm{poly}(n, \log|F|)$.
--
--   The list size is weaker than in Theorem 1.2, but the points are strongly explicit: each point costs time polylogarithmic in the field size, with no search over $K$.
--
--   **Formalization Note** $K = \mathbb F_p[Y]/(f)$ is input as $p, f$. The output field is $F = K[X]/(h)$ for one monic irreducible $h$ of degree at most $D$, so $|F| = |K|^{\deg h}$, and the points are written in the power basis of $F/K$. On input $(K, n, i)$ with $i < n$, one machine $M_{\mathrm{pt}}$ outputs $h$ and the coordinates of $\alpha_i$ within $c(\lfloor\log_2|F|\rfloor + 2)^c$ steps, with the same $h$ for every $i$. The list bound $(1/\varepsilon)^{O(1/\varepsilon)}$ is $(1/\varepsilon)^{c/\varepsilon}$, entered through its floor. The decoder reads $K, n, k$, $h$, the points and $y$, and outputs exactly the codewords within relative distance $1 - k/n - \varepsilon$ of $y$, each once, within $B(n + \lfloor\log_2|F|\rfloor + 2)^c$ steps. The constant $c$ is absolute; $M_{\mathrm{pt}}$, $M_{\mathrm{dec}}$, $N$, $D$, $B$ are chosen after $\varepsilon$.
--
--   Differences from the source:
--   - reading: an arbitrary field K of size at least n → a finite field K with n ≤ |K|; reason: |K| and |F| enter the time bounds, so K is finite
--   - reading: a strongly explicit construction of F and the points; "given an index i ∈ [n], α_i can be computed in time poly(log |F|)" → one machine that on input (K, n, i) outputs a monic irreducible h with F = K[X]/(h), the same for all i, and α_i in the power basis, within c(⌊log₂|F|⌋ + 2)^c steps; reason: strongly explicit means every part of the output is computable from the index in time polylogarithmic in |F|; every finite extension of K is K[X]/(h) for such an h
--   - encoding: a finite field K and a deterministic construction or algorithm with a running time → K = 𝔽_p[Y]/(f) input as p and a monic irreducible f; F = K[X]/(h) for a monic irreducible h; field elements by power-basis coordinates decoded structurally; one multi-stack Turing machine with an explicit step bound; reason: the base mission's published machine model; every finite field and every finite extension is isomorphic to one of these
--   - encoding: "the list can be found"; (1/ε)^{O(1/ε)}; poly(·); O_ε(1) → the decoder reads K, n, k, h, the points and y and outputs exactly the codewords within distance 1 − k/n − ε, each once; (1/ε)^{c/ε} with absolute c (its floor as the integer list bound); (·)^c with absolute c; a multiplier B chosen after ε; reason: the paper's constant conventions written out; the list is the list of the list-decoding claim
-- source:
--   Alrabiah–Goyal–Guruswami, Explicit Reed-Solomon Subspace Designs: Optimal List and Line Decoding, arXiv:2610.36215 (held version, sha256 cf26424b…f36206), Theorem 1.3, p.22 (PDF 24), also p.5 (PDF 7); proved p.23 (PDF 25)

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

/-- **Theorem 1.3 (Strongly explicit list-decodable Reed-Solomon codes).** Alrabiah–Goyal–
Guruswami, arXiv:2610.36215 (held version, sha256 cf26424b…f36206), Theorem 1.3, p.22 (also p.5;
proved p.23 from Theorems 7.1 and 5.1).

Fix `ε ∈ (0, 1)`. For all sufficiently large `n`, and an arbitrary field `K` of size at least `n`,
there is a strongly explicit construction of an extension field `F` over `K` with `[F : K] = O_ε(1)`
and evaluation points `A = (α₁, …, αₙ) ∈ Fⁿ`, such that for every `1 ≤ k ≤ n` the Reed–Solomon code
`RS_F(A, k)` of rate `R = k/n` is `(1 − R − ε, (1/ε)^{O(1/ε)})` list-decodable, and the list can be
found deterministically in time `O_ε(1) poly(n, log |F|)`. Given an index `i ∈ [n]`, `αᵢ` can be
computed in time `poly(log |F|)`.

**Formalization Note.** `K` is input as `p, f` (`K = AdjoinRoot f`, finite). The output field is
`F = K[X]/(h)` for a monic irreducible `h` of degree `≤ D`, `|F| = |K|^{deg h}`; points are written
in the power basis of `F/K` and decoded structurally. "Strongly explicit": one machine `M_pt` that on
input `(K, n, i)`, `i < n`, outputs `h` and the coordinates of `αᵢ` within `c(⌊log₂|F|⌋ + 2)^c`
steps; `h` is the same for every `i`. The constant `c` (of `poly` and of `(1/ε)^{O(1/ε)}`, written
`(1/ε)^{c/ε}`) is absolute and chosen first; `M_pt`, `M_dec`, `N`, `D` and the multiplier `B` of
`O_ε(1)` are chosen after `ε`. The decoder reads `K, n, k`, `h`, the points and `y`, and outputs,
without repetition, exactly the codewords within relative distance `1 − k/n − ε` of `y` (the list
of the list-decoding claim). List decodability is Definition 2.2 (`IsListDecodable`); the real
list bound `(1/ε)^{c/ε}` enters as its floor, which is equivalent for an integer size. -/
theorem theorem_1_3 :
    ∃ c : ℕ, ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ (Mpt Mdec : Turing.TM2ComputableAux Bool Bool) (N D B : ℕ),
        ∀ n : ℕ, N ≤ n →
        ∀ (p : ℕ) [Fact p.Prime] (f : (ZMod p)[X]) [Fact (Irreducible f)], f.Monic →
          n ≤ p ^ f.natDegree →
          ∃ (hc : List (List ℕ)) (ac : List (List (List ℕ))),
            IsCoeffList p f ((decPoly p f hc).natDegree + 1) hc ∧
            ac.length = n ∧ (∀ x ∈ ac, IsCoeffList p f (decPoly p f hc).natDegree x) ∧
            (decPoly p f hc).Monic ∧ (decPoly p f hc).natDegree ≤ D ∧
            (∀ i : ℕ, i < n →
              HMBinPacking.OutputsWithin Mpt (encField p f ++ encNat n ++ encNat i)
                (encList (encList encNat) hc ++ encList (encList encNat) (ac.getD i []))
                (c * (Nat.log 2 ((p ^ f.natDegree) ^ (decPoly p f hc).natDegree) + 2) ^ c)) ∧
            ∃ hirr : Irreducible (decPoly p f hc),
            haveI : Fact (Irreducible (decPoly p f hc)) := ⟨hirr⟩
            ∃ hα : Function.Injective fun i : Fin n =>
                AdjoinRoot.mk (decPoly p f hc) (decPoly p f (ac.getD i [])),
              ∀ k : ℕ, 1 ≤ k → k ≤ n →
                IsListDecodable (ReedSolomon.code ⟨_, hα⟩ k : Set (Fin n → AdjoinRoot (decPoly p f hc)))
                  (1 - (k : ℝ) / n - ε) ⌊(1 / ε) ^ ((c : ℝ) / ε)⌋₊ ∧
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
                      (B * (n + Nat.log 2 ((p ^ f.natDegree) ^ (decPoly p f hc).natDegree) + 2) ^ c) ∧
                    let dec : List (List (List ℕ)) → Fin n → AdjoinRoot (decPoly p f hc) :=
                      fun w i => AdjoinRoot.mk (decPoly p f hc) (decPoly p f (w.getD i []));
                    (out.map dec).Nodup ∧
                    ∀ w : Fin n → AdjoinRoot (decPoly p f hc),
                      w ∈ out.map dec ↔
                        (w ∈ ReedSolomon.code ⟨_, hα⟩ k ∧
                          relDist w (dec yc) ≤ 1 - (k : ℝ) / n - ε) := by sorry

end Supplement

end RSSubspaceDesign
