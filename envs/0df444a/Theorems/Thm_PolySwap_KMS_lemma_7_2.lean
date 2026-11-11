-- Prove2me | Theorems.Thm_PolySwap_KMS_lemma_7_2
-- name    : PolySwap.KMS.lemma_7_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:41:46.896516+00:00
-- url     : https://prove2.me/theorems/7c9b12d5-cea0-401e-9b36-81811e7c55de
-- title:
--   Lemma 7.2 (= Lemma 3.26) — $\mathrm{Dehn}_{Y_\ell}(s)\le As$ with a universal constant $A$
-- statement:
--   There is a universal constant $A$ such that for every nice set $\mathcal I$ of $T$ disjoint colour sets of size $r+1$ in $[d]$, every finite field $\mathbb F_q$, every $J\in\mathcal I$, every $0\le\ell\le r$ and every $s\in\mathbb N$,
--   $$\mathrm{Dehn}_{S_\ell,R_\ell}(s)\le As,$$
--   the Dehn function of the coset-complex presentation of the bin factor $Y_\ell=CC(U_{B_\ell};(H^{B_\ell}_I)_{I\in\mathcal I\setminus\{J\}})$ ($S_\ell=\bigcup_IH^{B_\ell}_I$, $R_\ell=\bigcup_IR^\ell_I$). The same statement is printed as Lemma 3.26, p. 29.
--
--   Differences from the source:
--   - encoding: a constant A (real), universal (Lemma 3.26) → ∃ A : ℕ before every parameter; reason: Dehn values are integers, so a real A can be replaced by ⌈A⌉
--   - encoding: every s ∈ ℕ (ℕ positive) → ∀ s : ℕ, including s = 0; reason: Dehn(0) = 0; no instance changes
--   - encoding: a prime power q = p^m and the field F_q → a finite field F (Fintype F) with q = Fintype.card F and p = ringChar F; reason: every finite field has prime-power order q and prime characteristic p; same instances
--   - encoding: a nice set I ∈ ([d] choose r+1)^[T] of disjoint colours (§6, §7 standing) and J ∈ I → I ∈ disjointColorSets d r T, IsNice d I, J ∈ I; bins indexed by ℓ ≤ r with B_ℓ = [binLo, binHi]; reason: the section's standing assumptions as binders
--   - reading: the vertex link (F^I X)_{gH_J} ≅ CC(U_{[d]∖J}; (U_{[d]∖(J∪I)})_{I∈I∖{J}}) in the upper-triangular model of §3.3, with the colours cyclically relabelled so that a chosen j₀ ∈ J becomes 0 (Definition 3.6) → linkY / binY: subgroups UL d F B = ⟨e_{i,i+1}(λ) : i ∈ B⟩ of SL_{d+1}(F_q) with the relabelling j₀ = min J (`base J`); reason: Definition 3.6 lets j₀ ∈ J be chosen and states the conditions do not depend on the choice; the least element is one such choice
--   - reading: condition (e) of Definition 3.6: 'for every pair of J-bins B, B′' → IsNice quantifies (e) over every pair (ℓ, ℓ′) of nonempty bins, B = B′ included; empty bins are omitted, as the definition says; reason: a pair is an arbitrary pair, as the proof of Lemma 3.7 counts it (p. 34: 'This count allows the two bins to belong to arbitrary color sets, as in the definition'); reading it as two different bins would weaken Lemma 3.7
--   - reading: Definition 2.35: generators 'all the elements of the H_i', relations R_i 'all the nontrivial relations in the multiplication table of H_i of length at most 3' (Appendix B, p. 61, writes S = ⋃H_i ∖ {1}) → cosetDehn: letters = the elements of ⋃_i H_i ∖ {1}; R_i = the positive words [a][b], [a][b][c] with letters in H_i ∖ {1} whose product is 1; reason: Appendix B (pp. 61–62), where Theorem 3.19 is proved, fixes S = ⋃H_i ∖ {1} and uses exactly the relations [g][g⁻¹] = 1 and the three-letter triangle words
--   - encoding: Dehn functions, areas, radii and diameters with values in ℕ (a max over a finite set) → values in ℕ∞ (iSup/iInf; ⊤ when there is no filling or path); reason: no junk value 0 for an empty or unbounded set; equal to the paper's value whenever that is finite
-- source:
--   Dikstein, Oppenheim, Valentiner-Branth, Polynomial Swap Coboundary Expansion with Applications to LTCs and PCPs, STOC 2027 submission (manuscript sha256 b9cb2095…), Lemma 7.2, p. 50 (= Lemma 3.26, p. 29)

import Mathlib
import Definitions.Def_PolySwap_KMS_Complex
import Definitions.Def_PolySwap_KMS_Dehn
import Definitions.Def_PolySwap_KMS_KMSComplex

namespace PolySwap.KMS

/-- **Lemma 7.2** (= Lemma 3.26, p. 29), p. 50. There is a constant `A` (universal) such that for
every nice set `I` of disjoint colour sets, every `J ∈ I`, every `0 ≤ ℓ ≤ r` and every `s ∈ ℕ`,
`Dehn_{S_ℓ,R_ℓ}(s) ≤ A s`, the Dehn function of the coset-complex presentation of the bin factor
`Y_ℓ = CC(U_{B_ℓ}; (H^{B_ℓ}_I)_{I ∈ I \ {J}})`. -/
theorem lemma_7_2 : ∃ A : ℕ, ∀ (d r T : ℕ) (F : Type*) [Field F] [Fintype F]
    (I : Finset (Finset ℕ)), I ∈ disjointColorSets d r T → IsNice d I →
    ∀ J ∈ I, ∀ ℓ ≤ r, ∀ s : ℕ, binDehn d F I J ℓ s ≤ (A : ℕ∞) * s := by sorry

end PolySwap.KMS
