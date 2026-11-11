-- Prove2me | Theorems.Thm_PolySwap_KMS_claim_6_2
-- name    : PolySwap.KMS.claim_6_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:41:30.312773+00:00
-- url     : https://prove2.me/theorems/022913d0-d74e-4a19-9e1e-f90953fc5daf
-- title:
--   Claim 6.2 — splitting $g\in H^{B_\ell}_I$ into $\le p(C)$ factors of block size $\le(b-a)/C$ with $\le p(C)$ relations
-- statement:
--   Let $\mathcal I$ be a nice set of $T$ disjoint colour sets of size $r+1$ in $[d]$, $J\in\mathcal I$, and work in $J$'s path order. There is a universal polynomial $p$ (independent of $\ell$, $r$ and the bin $[a,b]$) such that for every $0\le\ell\le r$ with $B_\ell=[a,b]$, every $C\in\mathbb N$ with $1\le C\le20$, every $I\in\mathcal I\setminus\{J\}$ and every $g\in H^{B_\ell}_I$ there are $g_1,\dots,g_s\in H^{B_\ell}_I$ with $s\le p(C)$, $g=g_1\cdots g_s$ and each $g_i$ supported on block size $\le\frac{b-a}{C}$. Moreover $g$ can be transformed into $g_1\cdots g_s$ by applying at most $p(C)$ relations of $R^\ell_I$, the multiplication-table relations of $H^{B_\ell}_I$.
--
--   Differences from the source:
--   - encoding: a universal polynomial p (independent of ℓ, r, [a, b]) → ∃ p : Polynomial ℕ before d, r, T, F, I, J, ℓ; reason: universal: independent of every parameter (the proof gives p(C) = 6²C¹⁸)
--   - encoding: g can be transformed into g₁⋯g_s by applying at most p(C) relations in R^ℓ_I → area (multTable (binH …) I) (cosetWord g · ([g₁]⋯[g_s])⁻¹) ≤ p(C) in the free group on the generators S_ℓ = ⋃H^{B_ℓ}_I ∖ {1} of Y_ℓ, where cosetWord g is the letter [g] (the empty word for g = 1, which is not a generator); reason: a word can be deduced from another with k relation applications (free moves not counted) iff their quotient has area ≤ k
--   - encoding: a prime power q = p^m and the field F_q → a finite field F (Fintype F) with q = Fintype.card F and p = ringChar F; reason: every finite field has prime-power order q and prime characteristic p; same instances
--   - encoding: a nice set I ∈ ([d] choose r+1)^[T] of disjoint colours (§6, §7 standing) and J ∈ I → I ∈ disjointColorSets d r T, IsNice d I, J ∈ I; bins indexed by ℓ ≤ r with B_ℓ = [binLo, binHi]; reason: the section's standing assumptions as binders
--   - reading: the vertex link (F^I X)_{gH_J} ≅ CC(U_{[d]∖J}; (U_{[d]∖(J∪I)})_{I∈I∖{J}}) in the upper-triangular model of §3.3, with the colours cyclically relabelled so that a chosen j₀ ∈ J becomes 0 (Definition 3.6) → linkY / binY: subgroups UL d F B = ⟨e_{i,i+1}(λ) : i ∈ B⟩ of SL_{d+1}(F_q) with the relabelling j₀ = min J (`base J`); reason: Definition 3.6 lets j₀ ∈ J be chosen and states the conditions do not depend on the choice; the least element is one such choice
--   - reading: condition (e) of Definition 3.6: 'for every pair of J-bins B, B′' → IsNice quantifies (e) over every pair (ℓ, ℓ′) of nonempty bins, B = B′ included; empty bins are omitted, as the definition says; reason: a pair is an arbitrary pair, as the proof of Lemma 3.7 counts it (p. 34: 'This count allows the two bins to belong to arbitrary color sets, as in the definition'); reading it as two different bins would weaken Lemma 3.7
--   - reading: Definition 2.35: generators 'all the elements of the H_i', relations R_i 'all the nontrivial relations in the multiplication table of H_i of length at most 3' (Appendix B, p. 61, writes S = ⋃H_i ∖ {1}) → cosetDehn: letters = the elements of ⋃_i H_i ∖ {1}; R_i = the positive words [a][b], [a][b][c] with letters in H_i ∖ {1} whose product is 1; reason: Appendix B (pp. 61–62), where Theorem 3.19 is proved, fixes S = ⋃H_i ∖ {1} and uses exactly the relations [g][g⁻¹] = 1 and the three-letter triangle words
--   - encoding: Dehn functions, areas, radii and diameters with values in ℕ (a max over a finite set) → values in ℕ∞ (iSup/iInf; ⊤ when there is no filling or path); reason: no junk value 0 for an empty or unbounded set; equal to the paper's value whenever that is finite
-- source:
--   Dikstein, Oppenheim, Valentiner-Branth, Polynomial Swap Coboundary Expansion with Applications to LTCs and PCPs, STOC 2027 submission (manuscript sha256 b9cb2095…), Claim 6.2, p. 47

import Mathlib
import Definitions.Def_PolySwap_KMS_Complex
import Definitions.Def_PolySwap_KMS_Dehn
import Definitions.Def_PolySwap_KMS_KMSComplex

namespace PolySwap.KMS

/-- **Claim 6.2**, p. 47. There is a universal polynomial `p` (independent of `ℓ`, `r`, the bin
`[a, b]`, and of `d`, `q`, `T`, `I`, `J`) such that: for every nice set `I` of disjoint colour
sets, every `J ∈ I`, every `0 ≤ ℓ ≤ r` with `B_ℓ = [a, b]`, every `C ∈ ℕ` with `1 ≤ C ≤ 20`,
every `I' ∈ I \ {J}` and every `g ∈ H^{B_ℓ}_{I'}`, there are `g₁, …, g_s ∈ H^{B_ℓ}_{I'}` with
`s ≤ p(C)`, `g = g₁ ⋯ g_s`, each `g_i` supported on block size `≤ (b - a)/C`, and `g` can be
transformed into `g₁ ⋯ g_s` by at most `p(C)` relations of `R^ℓ_{I'}`. -/
theorem claim_6_2 : ∃ p : Polynomial ℕ, ∀ (d r T : ℕ) (F : Type*) [Field F] [Fintype F]
    (I : Finset (Finset ℕ)), I ∈ disjointColorSets d r T → IsNice d I →
    ∀ J ∈ I, ∀ ℓ ≤ r, ∀ C : ℕ, 1 ≤ C → C ≤ 20 → ∀ K : {K // K ∈ I.erase J},
    ∀ g, (hg : g ∈ binH d F I J ℓ K) →
      ∃ gs : List (CosetGen (binH d F I J ℓ)), gs.length ≤ p.eval C ∧
        (∀ x ∈ gs, x.1 ∈ binH d F I J ℓ K) ∧ (gs.map Subtype.val).prod = g ∧
        (∀ x ∈ gs, ∃ k : ℕ, (k : ℝ) ≤ ((binHi d J ℓ : ℝ) - binLo d J ℓ) / C ∧
          SupportedOnBlock d F
            (((x.1 : UL d F (bin d J ℓ)) : Matrix.SpecialLinearGroup (Fin (d + 1)) F) :
              Matrix (Fin (d + 1)) (Fin (d + 1)) F) k) ∧
        area (multTable (binH d F I J ℓ) K)
            (cosetWord (binH d F I J ℓ) g ⟨K, hg⟩ *
              ((gs.map FreeGroup.of).prod)⁻¹) ≤ ((p.eval C : ℕ) : ℕ∞) := by sorry

end PolySwap.KMS
