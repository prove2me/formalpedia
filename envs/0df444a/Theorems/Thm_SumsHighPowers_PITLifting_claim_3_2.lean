-- Prove2me | Theorems.Thm_SumsHighPowers_PITLifting_claim_3_2
-- name    : SumsHighPowers.PITLifting.claim_3_2
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-10T16:10:58.987284+00:00
-- url     : https://prove2.me/theorems/deb82914-3f5c-4317-86da-1619b5dbb971
-- title:
--   Claim 3.2 — composing with the curve through a hitting set of $\Sigma^2C_\Delta$ keeps non-associates non-associate
-- statement:
--   Let $F$ be a field, $C\subseteq F[x_1,\dots,x_n]$ a class of polynomials and $\Delta,s\in\mathbb N$. Let $C_\Delta$ be the members of $C$ of total degree at most $\Delta$ and $\Sigma^2C_\Delta=\{\alpha_1g_1+\alpha_2g_2:\alpha_i\in F,\ g_i\in C_\Delta\}$. Suppose $u_1,\dots,u_s\in F^n$ is a hitting set for $\Sigma^2C_\Delta$ (every nonzero member is nonzero at some $u_i$), let $a_1,\dots,a_s\in F$ be pairwise distinct, and let $H=(H_1,\dots,H_n)\in F[t]^n$ be the curve with $\deg H_j\le s-1$ and $H(a_i)=u_i$ for all $i$. Then for all $A,B\in C_\Delta$:
--   $$A\not\sim B\ \Longrightarrow\ A\circ H\not\sim B\circ H,$$
--   where $\not\sim$ means non-associate (pairwise linearly independent, p. 12) and $A\circ H=A(H_1(t),\dots,H_n(t))\in F[t]$.
--
--   No assumption on the characteristic is needed (Remark 3.3). The claim is the step of the proof of Theorem 3.1 that turns pairwise non-associate multivariate polynomials into pairwise non-associate univariate ones, to which Theorem 2.10 applies.
--
--   **Formalization Note.** The setting is that of Theorem 3.1, written as hypotheses; $A\circ H$ is `MvPolynomial.aeval H A`.
--
--   Differences from the source:
--   - reading: A, B nonassociates; A ∘ H ≁ B ∘ H (associate: g = αf for nonzero f, g and nonzero α) → `PairwiseNonAssociate`: any two members with distinct indices are linearly independent over F; reason: the paper states on p. 12 that non-associate is equivalent to pairwise linearly independent; the reading also makes every member nonzero, without which the statement would fail (a zero member)
--   - encoding: the setting of Theorem 3.1, in force inside its proof where Claim 3.2 is stated → hypotheses `hu`, `ha`, `hHdeg`, `hHint` as in theorem_3_1 (without the characteristic and the r, d conditions); reason: Remark 3.3: the claim needs no characteristic bound, and r, d do not occur in it
--   - generalization: C is a polynomial class closed under scalar multiplications → `C` is an arbitrary set of polynomials (no closure hypothesis); reason: Σ²C_Δ is defined with scalars (p. 4), so α·g ∈ Σ²C_Δ for every g ∈ C_Δ without any hypothesis on C, which is the only use of the closure in the proof; a class closed under scalar multiplications is an instance
--   - generalization: a hitting set H = {u_1, …, u_s} for Σ²C_Δ of size s (a set, ordered arbitrarily) → a family `u : Fin s → (Fin n → F)` with `IsHittingSet (sumPowClass 2 1 (degBounded C Δ)) u`, repetitions allowed; reason: an injective family is exactly the paper's ordered set of size s; the statement is proved for every family
--   - encoding: H(t) the unique polynomial map whose coordinates have degree at most s − 1 and H(a_i) = u_i, with a_1, …, a_s pairwise distinct → any `H : Fin n → F[X]` with `(H j).degree < s` and `(H j).eval (a i) = u i j` for all i, j, and `a` injective; reason: by Lagrange interpolation such an H exists and is unique, so the hypotheses pin down the paper's curve; for s = 0 they force H = 0
--   - encoding: a class C ⊆ F[x_1, …, x_n]; C_Δ (total degree ≤ Δ); Σ^r ∧^d C_Δ and Σ²C_Δ (p. 4, p. 12) → `C : Set (MvPolynomial (Fin n) F)`, `degBounded C Δ` (totalDegree ≤ Δ), `sumPowClass r d (degBounded C Δ)` and `sumPowClass 2 1 (degBounded C Δ)`; reason: the paper's definitions, with variables indexed by Fin n and summands by Fin r
--   - encoding: A ∘ H, the composition of a polynomial with the curve → `MvPolynomial.aeval H A : F[X]`; reason: aeval substitutes H j for x_j; same polynomial in t
-- source:
--   Kaplan, Shpilka, Tal, PIT and Reconstruction for Sums of High Powers, STOC 2027 submission (manuscript, sha256 63d31ceb…9b604b19), p. 30, Claim 3.2 (in the proof of Theorem 3.1, p. 29; Remark 3.3)

import Mathlib
import Definitions.Def_SumsHighPowers_PITLifting_SumPowClass
import Definitions.Def_SumsHighPowers_PITLifting_IsHittingSet
import Definitions.Def_SumsHighPowers_PITLifting_PairwiseNonAssociate

namespace SumsHighPowers.PITLifting

/-- **Claim 3.2** (Kaplan–Shpilka–Tal, p. 30, inside the proof of Theorem 3.1), in the setting of
Theorem 3.1 (p. 29): `u₁, …, u_s ∈ Fⁿ` is a hitting set for `Σ²C_Δ`, `a₁, …, a_s ∈ F` are pairwise
distinct and `H ∈ F[t]ⁿ` has coordinates of degree at most `s − 1` with `H(aᵢ) = uᵢ`.
Let `A, B ∈ C_Δ` be non-associates. Then `A ∘ H` and `B ∘ H` are non-associates. No characteristic
hypothesis (Remark 3.3). -/
theorem claim_3_2 {F : Type*} [Field F] (n Δ s : ℕ)
    (C : Set (MvPolynomial (Fin n) F))
    (u : Fin s → Fin n → F) (hu : IsHittingSet (sumPowClass 2 1 (degBounded C Δ)) u)
    (a : Fin s → F) (ha : Function.Injective a)
    (H : Fin n → Polynomial F) (hHdeg : ∀ j, (H j).degree < s)
    (hHint : ∀ i j, (H j).eval (a i) = u i j)
    (A B : MvPolynomial (Fin n) F) (hA : A ∈ degBounded C Δ) (hB : B ∈ degBounded C Δ)
    (hAB : PairwiseNonAssociate (F := F) ![A, B]) :
    PairwiseNonAssociate (F := F) ![MvPolynomial.aeval H A, MvPolynomial.aeval H B] := by sorry

end SumsHighPowers.PITLifting
