-- Prove2me | Theorems.Thm_PolySwap_KMS_proposition_7_1
-- name    : PolySwap.KMS.proposition_7_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:41:45.529565+00:00
-- url     : https://prove2.me/theorems/352ce31e-5dcc-4f21-b4ab-6201ca757a9c
-- title:
--   Proposition 7.1 (= Lemma 3.21) — $\mathrm{diam}(Y)\le6(r+1)+1$
-- statement:
--   Let $\mathcal I$ be a nice set of $T$ disjoint colour sets of size $r+1$ in $[d]$, $\mathbb F_q$ a finite field and $J\in\mathcal I$. Then the vertex link $Y=CC(U_{[d]\setminus J};(H^{[d]\setminus J}_I)_{I\in\mathcal I\setminus\{J\}})$ satisfies
--   $$\mathrm{diam}(Y)\le6(r+1)+1.$$
--   The same statement is printed as Lemma 3.21, p. 28.
--
--   Differences from the source:
--   - encoding: a prime power q = p^m and the field F_q → a finite field F (Fintype F) with q = Fintype.card F and p = ringChar F; reason: every finite field has prime-power order q and prime characteristic p; same instances
--   - encoding: a nice set I ∈ ([d] choose r+1)^[T] of disjoint colours (§6, §7 standing) and J ∈ I → I ∈ disjointColorSets d r T, IsNice d I, J ∈ I; bins indexed by ℓ ≤ r with B_ℓ = [binLo, binHi]; reason: the section's standing assumptions as binders
--   - reading: the vertex link (F^I X)_{gH_J} ≅ CC(U_{[d]∖J}; (U_{[d]∖(J∪I)})_{I∈I∖{J}}) in the upper-triangular model of §3.3, with the colours cyclically relabelled so that a chosen j₀ ∈ J becomes 0 (Definition 3.6) → linkY / binY: subgroups UL d F B = ⟨e_{i,i+1}(λ) : i ∈ B⟩ of SL_{d+1}(F_q) with the relabelling j₀ = min J (`base J`); reason: Definition 3.6 lets j₀ ∈ J be chosen and states the conditions do not depend on the choice; the least element is one such choice
--   - reading: condition (e) of Definition 3.6: 'for every pair of J-bins B, B′' → IsNice quantifies (e) over every pair (ℓ, ℓ′) of nonempty bins, B = B′ included; empty bins are omitted, as the definition says; reason: a pair is an arbitrary pair, as the proof of Lemma 3.7 counts it (p. 34: 'This count allows the two bins to belong to arbitrary color sets, as in the definition'); reading it as two different bins would weaken Lemma 3.7
--   - encoding: Dehn functions, areas, radii and diameters with values in ℕ (a max over a finite set) → values in ℕ∞ (iSup/iInf; ⊤ when there is no filling or path); reason: no junk value 0 for an empty or unbounded set; equal to the paper's value whenever that is finite
--   - encoding: the coset complex CC(G; (H_i)) with vertex set ⊔_i G/H_i (Definition 2.4) → cosetComplex G H : WComplex (Σ i, G ⧸ H i), maximal faces the chambers {gH_i : i}, uniform top weight; reason: Lean convention for ⊔_i G/H_i; same faces and weights
-- source:
--   Dikstein, Oppenheim, Valentiner-Branth, Polynomial Swap Coboundary Expansion with Applications to LTCs and PCPs, STOC 2027 submission (manuscript sha256 b9cb2095…), Proposition 7.1, p. 50 (= Lemma 3.21, p. 28)

import Mathlib
import Definitions.Def_PolySwap_KMS_Complex
import Definitions.Def_PolySwap_KMS_Cone
import Definitions.Def_PolySwap_KMS_Dehn
import Definitions.Def_PolySwap_KMS_KMSComplex

namespace PolySwap.KMS

/-- **Proposition 7.1** (= Lemma 3.21, p. 28), p. 50. For every nice set `I` of `T` disjoint
colour sets of size `r + 1` and every `J ∈ I`, the vertex link
`Y = CC(U_{[d]\J}; (H^{[d]\J}_I)_{I ∈ I \ {J}})` has `diam(Y) ≤ 6(r + 1) + 1`. -/
theorem proposition_7_1 (d r T : ℕ) (F : Type*) [Field F] [Fintype F]
    (I : Finset (Finset ℕ)) (hI : I ∈ disjointColorSets d r T) (hnice : IsNice d I)
    (J : Finset ℕ) (hJ : J ∈ I) :
    (linkY d F I J).diam ≤ ((6 * (r + 1) + 1 : ℕ) : ℕ∞) := by sorry

end PolySwap.KMS
