-- Prove2me | Theorems.Thm_RSSubspaceDesign_lemma_2_20_computation
-- name    : RSSubspaceDesign.lemma_2_20_computation
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:29:27.140794+00:00
-- url     : https://prove2.me/theorems/bf243298-f34f-45a0-94aa-0ea322b77075
-- title:
--   Lemma 2.20, last sentence — the set $B$ can be computed deterministically in polynomial time (companion of lemma\_2\_20)
-- statement:
--   Let $K\subseteq F$ be finite fields, let $\sigma_1,\dots,\sigma_g$ generate $\mathrm{Gal}(F/K)$, and let $u_1,\dots,u_d\in F[X]$ be linearly independent over $K(X)$, where $g,d\ge1$. A set $B\subseteq\mathbb Z_{\ge0}^g$ with the properties of Lemma 2.20 — size $d$, downward closed, $P(X)=\det(\sigma^\omega(u_a))_{\omega\in B,a\in[d]}\ne0$, and the bound (2.2) for all distinct points — can be computed deterministically in polynomial time.
--
--   This is the algorithmic sentence of Lemma 2.20; the existence part is `RSSubspaceDesign.lemma_2_20`.
--
--   **Formalization Note** One Turing machine and one absolute exponent $c$; the step bound is $(L+2)^c$ for input length $L$. The input is $K=\mathbb F_p[Y]/(f)$, $F=K[X]/(h)$ (coefficient lists of a monic irreducible $h$), each $\sigma_j$ by the image $\sigma_j(\text{root of }h)$, and each $u_a$ by its coefficient lists; the output is the list of the vectors $\omega\in B$, without repetition.
--
--   Differences from the source:
--   - encoding: finite fields K ⊆ F → K = 𝔽_p[Y]/(f) and F = K[X]/(h) (h monic irreducible), input as coefficient lists; reason: every finite extension of finite fields is isomorphic to one of these, and the statement is invariant under isomorphism
--   - reading: can be computed deterministically in polynomial time → one multi-stack Turing machine and one absolute c with step bound (L + 2)^c in the input length L; reason: the paper fixes no model; Turing machines simulate any reasonable deterministic model with polynomial overhead
--   - encoding: the automorphisms σ₁, …, σ_g and polynomials u₁, …, u_d given to the algorithm → σⱼ given by the point σⱼ(root of h) of F, uₐ by its coefficients, all in the power basis of F/K; reason: an automorphism of F/K is determined by the image of the root; any other standard representation (e.g. a Frobenius power) converts to this one in polynomial time
--   - encoding: the set B → the list of its vectors ω, each of length g, without repetition; reason: same set
-- source:
--   O. Alrabiah, R. Goyal, V. Guruswami, Explicit Reed-Solomon Subspace Designs: Optimal List and Line Decoding, arXiv:2610.36215 (held version, sha256 cf26424b…), Lemma 2.20, last sentence, p.15 (PDF p.17)

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_RSListDecodingCapacity_AllRates_Encoding
import Definitions.Def_RSSubspaceDesign_ratFuncAlgebra
import Definitions.Def_RSSubspaceDesign_IsConjugateSet
import Definitions.Def_RSSubspaceDesign_decPoly
import Definitions.Def_RSSubspaceDesign_IsCoeffList
import Definitions.Def_RSSubspaceDesign_encField

open Polynomial RSListDecodingCapacity.AllRates

namespace RSSubspaceDesign

/-- **Lemma 2.20, last sentence (computing `B`).** Alrabiah–Goyal–Guruswami, arXiv:2610.36215
(held version, sha256 cf26424b…f36206), Lemma 2.20, pp.14–15: "Such a set `B` can be computed
deterministically in polynomial time." Companion of `lemma_2_20` (properties (i)–(ii)).

Given finite fields `K ⊆ F`, generators `σ₁, …, σ_g` of `Gal(F/K)` and `u₁, …, u_d ∈ F[X]` linearly
independent over `K(X)` (`g, d ≥ 1`), a deterministic algorithm outputs, in time polynomial in the
input length, a set `B ⊆ ℤ^g_{≥0}` with the properties of Lemma 2.20 (`IsConjugateSet`).

**Formalization Note.** One multi-stack Turing machine `M` and one absolute exponent `c`; the time
bound is `(L + 2)^c` for input length `L`. Input: `K = 𝔽_p[Y]/(f)` (`encField`), then `F = K[X]/(h)`
as the `deg h + 1` coefficient lists of a monic irreducible `h`, then each `σⱼ` as the point
`σⱼ(root h)` (an automorphism of `F/K` is determined by the image of the root), then each `u_a`
as its list of coefficients, each a point of `F` in the power basis (`decPoly`, `IsCoeffList`,
decoding by `AdjoinRoot.mk`). Output: the list of the exponent vectors `ω ∈ B`, each of length `g`,
without repetition. -/
theorem lemma_2_20_computation :
    ∃ (c : ℕ) (M : Turing.TM2ComputableAux Bool Bool),
      ∀ (p : ℕ) [Fact p.Prime] (f : (ZMod p)[X]) [Fact (Irreducible f)], f.Monic →
      ∀ (hc : List (List ℕ)) [Fact (Irreducible (decPoly p f hc))],
        IsCoeffList p f ((decPoly p f hc).natDegree + 1) hc → (decPoly p f hc).Monic →
      ∀ (g d : ℕ), 1 ≤ g → 1 ≤ d →
      ∀ (sc : List (List (List ℕ))), sc.length = g →
        (∀ x ∈ sc, IsCoeffList p f (decPoly p f hc).natDegree x) →
      ∀ (σ : Fin g → (AdjoinRoot (decPoly p f hc) ≃ₐ[AdjoinRoot f] AdjoinRoot (decPoly p f hc))),
        (∀ j : Fin g, σ j (AdjoinRoot.root (decPoly p f hc)) =
          AdjoinRoot.mk (decPoly p f hc) (decPoly p f (sc.getD j []))) →
        Subgroup.closure (Set.range σ) = ⊤ →
      ∀ (uc : List (List (List (List ℕ)))), uc.length = d →
        (∀ v ∈ uc, ∀ x ∈ v, IsCoeffList p f (decPoly p f hc).natDegree x) →
        (letI := ratFuncAlgebra (AdjoinRoot f) (AdjoinRoot (decPoly p f hc));
          LinearIndependent (RatFunc (AdjoinRoot f)) fun a : Fin d =>
            algebraMap (AdjoinRoot (decPoly p f hc))[X] (RatFunc (AdjoinRoot (decPoly p f hc)))
              (∑ i : Fin (uc.getD a []).length,
                C (AdjoinRoot.mk (decPoly p f hc) (decPoly p f ((uc.getD a []).get i))) *
                  X ^ (i : ℕ))) →
        ∃ Bl : List (List ℕ),
          HMBinPacking.OutputsWithin M
            (encField p f ++ encList (encList encNat) hc ++
              encList (encList (encList encNat)) sc ++
              encList (encList (encList (encList encNat))) uc)
            (encList (encList encNat) Bl)
            (((encField p f ++ encList (encList encNat) hc ++
              encList (encList (encList encNat)) sc ++
              encList (encList (encList (encList encNat))) uc).length + 2) ^ c) ∧
          Bl.Nodup ∧ (∀ l ∈ Bl, l.length = g) ∧
          IsConjugateSet (AdjoinRoot f) σ
            (fun a : Fin d => ∑ i : Fin (uc.getD a []).length,
              C (AdjoinRoot.mk (decPoly p f hc) (decPoly p f ((uc.getD a []).get i))) * X ^ (i : ℕ))
            (Bl.map fun l => fun j : Fin g => l.getD j 0).toFinset := by sorry

end RSSubspaceDesign
