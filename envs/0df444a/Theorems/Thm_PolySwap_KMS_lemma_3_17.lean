-- Prove2me | Theorems.Thm_PolySwap_KMS_lemma_3_17
-- name    : PolySwap.KMS.lemma_3_17
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:41:56.898452+00:00
-- url     : https://prove2.me/theorems/56c3d395-f884-4e39-9a74-60c9b3df168b
-- title:
--   Lemma 3.17 — the links $CC(U_{[d]\setminus J};(U_{[d]\setminus(J\cup I)}))$ are connected for $|\mathcal I|\ge3$ and 1-connected for $|\mathcal I|\ge4$
-- statement:
--   Assume the field size satisfies $q\ge5$. Let $\mathcal I$ be a set of disjoint colour sets of size $r+1$ in $[d]$ and $J\in\mathcal I$. The complex
--   $$CC\big(U_{[d]\setminus J};(U_{[d]\setminus(J\cup I)})_{I\in\mathcal I\setminus\{J\}}\big)$$
--   is connected if $|\mathcal I|\ge3$ and 1-connected if $|\mathcal I|\ge4$. Thus in particular, if $|\mathcal I|\ge4$, then $H^1\big((F^{\mathcal I}X)_{gH_J},\Lambda\big)=1$ for $X=X(A_d,\mathbb F_q,f)$ ($f$ irreducible of degree $\ge2$), every vertex $gH_J$ of $F^{\mathcal I}X$ of colour $J$ and every group $\Lambda$.
--
--   Differences from the source:
--   - encoding: a prime power q = p^m and the field F_q → a finite field F (Fintype F) with q = Fintype.card F and p = ringChar F; reason: every finite field has prime-power order q and prime characteristic p; same instances
--   - encoding: d ≥ 2 and 1 ≤ r ≤ d (§2.3 and Definition 2.14 standing assumptions); I a set of T disjoint colour sets (the §3.3 setting) → hypotheses 2 ≤ d, 1 ≤ r and I ∈ disjointColorSets d r T; |I| = I.card; reason: the standing assumptions as binders
--   - reading: the vertex link (F^I X)_{gH_J} ≅ CC(U_{[d]∖J}; (U_{[d]∖(J∪I)})_{I∈I∖{J}}) in the upper-triangular model of §3.3, with the colours cyclically relabelled so that a chosen j₀ ∈ J becomes 0 (Definition 3.6) → linkY / binY: subgroups UL d F B = ⟨e_{i,i+1}(λ) : i ∈ B⟩ of SL_{d+1}(F_q) with the relabelling j₀ = min J (`base J`); reason: Definition 3.6 lets j₀ ∈ J be chosen and states the conditions do not depend on the choice; the least element is one such choice
--   - encoding: X(A_d, F_q, f) = CC(SL_{d+1}(F_q[t]/(f)); (π_f(U_{[d]∖{i}}))_{i∈[d]}) with the uniform top-level distribution → kmsX d F f: cosetComplex over SL (Fin (d+1)) (AdjoinRoot f) of Hf d F f i = (U d F ([d]∖{i})).map (SpecialLinearGroup.map (AdjoinRoot.mk f)), vertices ⟨i, gH^f_i⟩ : Σ i, G ⧸ H^f_i, colour i; reason: Lean convention (0-based matrix indices, F_q[t]/(f) as AdjoinRoot f); the same complex and weights
--   - encoding: 1-connected (Definition 2.28) → IsOneConnected (combinatorial edge-path form, Remark 2.29); reason: the two notions coincide
--   - encoding: H¹(Y, Λ) = 1 (every orbit of a cocycle is that of the trivial cocycle, equivalently B¹ = Z¹) → H1Trivial: every 1-cocycle equals d₀g on every ordered edge for some 0-cochain g; reason: the paper's equivalence (p. 12); cochains are total functions and only their values on the complex count
--   - encoding: the coset complex CC(G; (H_i)) with vertex set ⊔_i G/H_i (Definition 2.4) → cosetComplex G H : WComplex (Σ i, G ⧸ H i), maximal faces the chambers {gH_i : i}, uniform top weight; reason: Lean convention for ⊔_i G/H_i; same faces and weights
-- source:
--   Dikstein, Oppenheim, Valentiner-Branth, Polynomial Swap Coboundary Expansion with Applications to LTCs and PCPs, STOC 2027 submission (manuscript sha256 b9cb2095…), Lemma 3.17, p. 27

import Mathlib
import Definitions.Def_PolySwap_KMS_Complex
import Definitions.Def_PolySwap_KMS_Cohomology
import Definitions.Def_PolySwap_KMS_Cone
import Definitions.Def_PolySwap_KMS_Dehn
import Definitions.Def_PolySwap_KMS_KMSComplex

open Polynomial

namespace PolySwap.KMS

/-- **Lemma 3.17**, p. 27. Let `q ≥ 5`, let `I` be a set of disjoint colour sets of size `r + 1`
and `J ∈ I`. The complex `Y = CC(U_{[d]\J}; (U_{[d]\(J ∪ I)})_{I ∈ I \ {J}})` is connected if
`|I| ≥ 3` and 1-connected if `|I| ≥ 4`. Thus in particular, if `|I| ≥ 4`, then
`H¹((F^I X)_{gH_J}, Λ) = 1` for `X = X(A_d, F_q, f)`, every vertex `gH_J` of colour `J` and every
group `Λ`. -/
theorem lemma_3_17 (d r T : ℕ) (hd : 2 ≤ d) (hr : 1 ≤ r) (F : Type*) [Field F] [Fintype F]
    (hq : 5 ≤ Fintype.card F) (I : Finset (Finset ℕ)) (hI : I ∈ disjointColorSets d r T)
    (J : Finset ℕ) (hJ : J ∈ I) :
    (3 ≤ I.card → (linkY d F I J).IsConnected) ∧
    (4 ≤ I.card → (linkY d F I J).IsOneConnected) ∧
    (4 ≤ I.card → ∀ f : F[X], Irreducible f → 2 ≤ f.natDegree →
      ∀ v ∈ (kmsFI d F f I).vertices, v.image (kmsCol d F f) = J →
        ∀ (Λ : Type*) [Group Λ], ((kmsFI d F f I).link {v}).H1Trivial Λ) := by sorry

end PolySwap.KMS
