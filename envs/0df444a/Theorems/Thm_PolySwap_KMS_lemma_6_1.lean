-- Prove2me | Theorems.Thm_PolySwap_KMS_lemma_6_1
-- name    : PolySwap.KMS.lemma_6_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:41:46.479915+00:00
-- url     : https://prove2.me/theorems/fc490982-ab4e-44cb-8fcd-1e6024387d87
-- title:
--   Lemma 6.1 (= Lemma 3.25) — direct product lemma: $\mathrm{Dehn}_Y(t)\le O((t(r+1))^2)+(r+1)At$
-- statement:
--   Let $\mathcal I$ be a nice set of $T$ disjoint colour sets of size $r+1$ in $[d]$ and $J\in\mathcal I$. Assume there is a constant $A$ with $\mathrm{Dehn}_{Y_\ell}(s)\le As$ for every $0\le\ell\le r$ and every $s\in\mathbb N$, each Dehn function taken for the coset-complex presentation of $Y_\ell$. Then, for the coset-complex presentation of $Y=CC(U_{[d]\setminus J};(H^{[d]\setminus J}_I)_{I\in\mathcal I\setminus\{J\}})$,
--   $$\mathrm{Dehn}_Y(t)\le O\big((t(r+1))^2\big)+(r+1)At\qquad\text{for every }t\in\mathbb N,$$
--   where the constant in $O(\cdot)$ is absolute. The same statement is printed as Lemma 3.25, p. 29.
--
--   Differences from the source:
--   - encoding: O((t(r+1))²) → K · (t(r+1))² with ∃ K : ℝ≥0 before every parameter (d, r, T, q, I, J, A, t); reason: the implied constant is absolute (the proof's O(1) per commutation comes from Claim 6.2 with C = 20); uniform reading
--   - encoding: a constant A → A : ℝ≥0, with Dehn values cast to ℝ≥0∞; reason: A < 0 is impossible under the hypothesis at s = 1, so nonnegativity loses nothing
--   - encoding: every s, t ∈ ℕ (ℕ positive) → ∀ s t : ℕ, including 0; reason: Dehn(0) = 0; no instance changes
--   - encoding: a prime power q = p^m and the field F_q → a finite field F (Fintype F) with q = Fintype.card F and p = ringChar F; reason: every finite field has prime-power order q and prime characteristic p; same instances
--   - encoding: a nice set I ∈ ([d] choose r+1)^[T] of disjoint colours (§6, §7 standing) and J ∈ I → I ∈ disjointColorSets d r T, IsNice d I, J ∈ I; bins indexed by ℓ ≤ r with B_ℓ = [binLo, binHi]; reason: the section's standing assumptions as binders
--   - reading: the vertex link (F^I X)_{gH_J} ≅ CC(U_{[d]∖J}; (U_{[d]∖(J∪I)})_{I∈I∖{J}}) in the upper-triangular model of §3.3, with the colours cyclically relabelled so that a chosen j₀ ∈ J becomes 0 (Definition 3.6) → linkY / binY: subgroups UL d F B = ⟨e_{i,i+1}(λ) : i ∈ B⟩ of SL_{d+1}(F_q) with the relabelling j₀ = min J (`base J`); reason: Definition 3.6 lets j₀ ∈ J be chosen and states the conditions do not depend on the choice; the least element is one such choice
--   - reading: condition (e) of Definition 3.6: 'for every pair of J-bins B, B′' → IsNice quantifies (e) over every pair (ℓ, ℓ′) of nonempty bins, B = B′ included; empty bins are omitted, as the definition says; reason: a pair is an arbitrary pair, as the proof of Lemma 3.7 counts it (p. 34: 'This count allows the two bins to belong to arbitrary color sets, as in the definition'); reading it as two different bins would weaken Lemma 3.7
--   - reading: Definition 2.35: generators 'all the elements of the H_i', relations R_i 'all the nontrivial relations in the multiplication table of H_i of length at most 3' (Appendix B, p. 61, writes S = ⋃H_i ∖ {1}) → cosetDehn: letters = the elements of ⋃_i H_i ∖ {1}; R_i = the positive words [a][b], [a][b][c] with letters in H_i ∖ {1} whose product is 1; reason: Appendix B (pp. 61–62), where Theorem 3.19 is proved, fixes S = ⋃H_i ∖ {1} and uses exactly the relations [g][g⁻¹] = 1 and the three-letter triangle words
--   - encoding: Dehn functions, areas, radii and diameters with values in ℕ (a max over a finite set) → values in ℕ∞ (iSup/iInf; ⊤ when there is no filling or path); reason: no junk value 0 for an empty or unbounded set; equal to the paper's value whenever that is finite
-- source:
--   Dikstein, Oppenheim, Valentiner-Branth, Polynomial Swap Coboundary Expansion with Applications to LTCs and PCPs, STOC 2027 submission (manuscript sha256 b9cb2095…), Lemma 6.1, p. 47 (= Lemma 3.25, p. 29)

import Mathlib
import Definitions.Def_PolySwap_KMS_Complex
import Definitions.Def_PolySwap_KMS_Dehn
import Definitions.Def_PolySwap_KMS_KMSComplex

open scoped ENNReal NNReal

namespace PolySwap.KMS

/-- **Lemma 6.1** (= Lemma 3.25, p. 29), p. 47 (direct product lemma). There is an absolute
constant `K` (the constant of `O((t(r+1))²)`, independent of `t`, `r`, `A`, `d`, `q`, `T`, `I`, `J`)
such that for every nice set `I` of disjoint colour sets and `J ∈ I`: if `A` is a constant with
`Dehn_{Y_ℓ}(s) ≤ A s` for every `0 ≤ ℓ ≤ r` and every `s`, then
`Dehn_Y(t) ≤ K (t(r+1))² + (r+1) A t` for every `t`, where `Y = CC(U_{[d]\J}; (H^{[d]\J}_I))` and
all Dehn functions are those of the coset-complex presentations. -/
theorem lemma_6_1 : ∃ K : ℝ≥0, ∀ (d r T : ℕ) (F : Type*) [Field F] [Fintype F]
    (I : Finset (Finset ℕ)), I ∈ disjointColorSets d r T → IsNice d I →
    ∀ J ∈ I, ∀ A : ℝ≥0, (∀ ℓ ≤ r, ∀ s : ℕ, (binDehn d F I J ℓ s : ℝ≥0∞) ≤ A * s) →
      ∀ t : ℕ, (linkDehn d F I J t : ℝ≥0∞) ≤
        K * ((t : ℝ≥0∞) * (r + 1)) ^ 2 + (r + 1) * A * t := by sorry

end PolySwap.KMS
