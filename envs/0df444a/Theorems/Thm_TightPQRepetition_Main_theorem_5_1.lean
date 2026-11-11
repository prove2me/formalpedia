-- Prove2me | Theorems.Thm_TightPQRepetition_Main_theorem_5_1
-- name    : TightPQRepetition.Main.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T23:43:08.408468+00:00
-- url     : https://prove2.me/theorems/3c8f3de1-1a68-4e0f-8f40-030d42a0d5c1
-- title:
--   Theorem 5.1 — quantum single-copy extraction
-- statement:
--   Let $(P,V)$ be an $m$-round protocol with $m$ polynomially bounded, under a semantically secure scheme. Suppose $B$ is a QPT prover, $k,k',t'$ are polynomially bounded functions, $\nu>0$ is an inverse polynomial, and $\varepsilon$ is efficiently computable with values in $[0,1]$, such that for all $\lambda\in\Lambda\subseteq\mathbb N$ we have $k\ge k'\ge t'$, $k'>1$,
--   $$\Pr[\langle B,\widehat V^{k',t'}\rangle(1^\lambda)=1]\ge B(k',t',\varepsilon)+\frac{10k'-1}{10k}\nu,$$
--   and with probability at least $1-\nu/10k$ over $r^*$ both conditional tail bounds of `TailBounds` hold. Then there are a QPT prover $A$ and a negligible function such that for all $\lambda\in\Lambda$,
--   $$\Pr[\langle A,V\rangle(1^\lambda)=1]\ge\varepsilon+\frac{\nu}{2k}-\mathrm{negl}(\lambda).$$
--   This is the main technical result: a prover that does well on many coordinates, without bad correlations with the first coordinate, is turned into a prover against the original protocol.
--
--   Differences from the source:
--   - generalization: PPT verifier and encryption algorithms (uniform) → non-uniform families of polynomial-size Boolean circuits, with coins an explicit input and outputs of bounded, input-dependent length; reason: a uniform PPT algorithm gives such a family, so every source instance is covered; the source already takes all adversaries non-uniform (Remark 5.2)
--   - encoding: QPT prover with quantum advice → a family of `Strategy`: a pure advice state, one unitary circuit of one- and two-qubit gates per round, computational-basis measurement of answer wires, and a polynomial-size classical controller with a random tape; reason: purification costs polynomial overhead (PDF p. 22); the source fixes no gate set
--   - generalization: polynomials k ≥ k′ ≥ t′, k′ > 1, inverse polynomial ν → polynomially bounded functions, with k ≥ k′ ≥ t′ and k′ > 1 required on Λ only; reason: Corollary 5.3 applies the theorem to the functions k′(λ), t′(λ) output by T, which are not polynomials; polynomials are a special case
--   - encoding: efficiently computable ε(λ) ≥ 0 → ε(λ) ∈ [0,1], efficiently computable by a polynomial-time Turing machine to any requested precision; reason: [0,1] is the domain of B(k,t,ε) in Notation 2
--   - generalization: the scheme is a QFHE of Definition 2, or an FHE of Definition 1 for Remark 3.3 → any `EncScheme`: efficient classical Gen, Enc, Dec with semantic security, with no homomorphic evaluation or correctness required; reason: the verifier and the soundness proof use only these; `ClassicalFHE.toEncScheme` and `QFHE.toEncScheme` give the source's two cases
--   - reading: queries q_j of unspecified length → each q_j has a length depending only on λ and j; reason: the dummy Enc(0) of Algorithm 1 is prepared before the query is known, and semantic security needs |m₀| = |m₁|, so the length must be known in advance; a verifier reaches this form by padding
--   - generalization: a positive inverse-polynomial parameter ν → any positive ν bounded below by the reciprocal of a positive polynomially bounded integer-valued function; reason: the bounds use polynomial boundedness of 1/ν; reciprocals of positive real polynomials are included by choosing an integer polynomial majorant of their denominators
-- source:
--   Zvika Brakerski, Andrew Huang, Yael Tauman Kalai, Nicholas Spooner, STOC 2027 submission #158 (October 2026), SHA-256 269f233ccbc44af16ba1b9aceb41299c2242cca048f65729c5fd3451cb6cd0b8, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/158.pdf, Theorem 5.1, printed pp. 18–19 / PDF pp. 20–21; proof printed pp. 20–32 / PDF pp. 22–34

import Mathlib
import Definitions.Def_TightPQRepetition_Main_Preprocess

namespace TightPQRepetition.Main

/-- Theorem 5.1 (printed pp. 18–19, PDF pp. 20–21). -/
theorem theorem_5_1 (E : EncScheme) (hE : E.IsEfficient) (hsec : E.IsSemanticallySecure)
    (V : Verifier) (hV : V.IsEfficient) (B : ℕ → Strategy) (hB : IsQPT B)
    (k k' t' : ℕ → ℕ) (hk : PolyBound k) (hk' : PolyBound k') (ht' : PolyBound t')
    (ν ε : ℕ → ℝ) (hν : InversePoly ν) (hεc : EfficientlyComputable ε)
    (hε0 : ∀ lam, 0 ≤ ε lam) (hε1 : ∀ lam, ε lam ≤ 1) (Λ : Set ℕ)
    (hkk : ∀ lam ∈ Λ, 1 < k' lam ∧ k' lam ≤ k lam ∧ t' lam ≤ k' lam)
    (hacc : ∀ lam ∈ Λ,
      binomTail (k' lam) (t' lam) (ε lam) + (10 * (k' lam : ℝ) - 1) / (10 * k lam) * ν lam ≤
        (B lam).acceptProb (hatPar E V (k' lam) (t' lam)) lam)
    (htail : ∀ lam ∈ Λ, TailBounds E V (B lam) lam (k lam) (k' lam) (t' lam) (ν lam) (ε lam)) :
    ∃ A : ℕ → Strategy, IsQPT A ∧ ∃ μ : ℕ → ℝ, Negligible μ ∧
      ∀ lam ∈ Λ, ε lam + ν lam / (2 * k lam) - μ lam ≤ (A lam).acceptProb V lam := by sorry

end TightPQRepetition.Main
