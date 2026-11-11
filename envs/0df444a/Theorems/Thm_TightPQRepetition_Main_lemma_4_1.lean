-- Prove2me | Theorems.Thm_TightPQRepetition_Main_lemma_4_1
-- name    : TightPQRepetition.Main.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T23:43:02.980709+00:00
-- url     : https://prove2.me/theorems/7f4419ba-99d2-4889-9db3-993d446c14e8
-- title:
--   Lemma 4.1 with Remark 4.2 — purification-oracle indistinguishability
-- statement:
--   Let $D_{0},D_{1}$ be efficiently sampleable on common registers and $|D_b\rangle$ their coherent states. Let $\Lambda\subseteq\mathbb N$. Suppose a polynomial-size oracle circuit $S$ with quantum advice, acting as the identity on $R$ between oracle calls, satisfies
--   $$\Big|\Pr[S^{U_0}(1^\lambda,|D_{0,\lambda}\rangle_{RE})=1]-\Pr[S^{U_1}(1^\lambda,|D_{1,\lambda}\rangle_{RE})=1]\Big|\ge\frac1{p(\lambda)}$$
--   for all $\lambda\in\Lambda$, with $p$ a polynomial. Then there is a polynomial-size quantum algorithm with quantum advice that distinguishes classical samples of $D_{0,\lambda}$ and $D_{1,\lambda}$ with advantage at least $1/p'(\lambda)$ on the same $\lambda\in\Lambda$, for a polynomial $p'$.
--
--   The oracle gives no help because the only way to see a difference through $U_b$ is to apply it to $|D_b\rangle$ itself, and $R$ is out of reach.
--
--   Differences from the source:
--   - generalization: Lemma 4.1 for all λ, with a uniform distinguisher → any set Λ of input lengths and quantum advice, the conclusion on the same Λ; reason: this is the extension of Remark 4.2 used by Lemma 4.3, and Λ = ℕ is the printed lemma
--   - generalization: efficiently sampleable distributions → samplers given by polynomial-size circuit families; reason: a uniform sampler gives such a family
--   - encoding: "distinguishes classical samples" → advantage at least the inverse of a polynomial; reason: the sense of the hypothesis
-- source:
--   Zvika Brakerski, Andrew Huang, Yael Tauman Kalai, Nicholas Spooner, STOC 2027 submission #158 (October 2026), SHA-256 269f233ccbc44af16ba1b9aceb41299c2242cca048f65729c5fd3451cb6cd0b8, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/158.pdf, Lemma 4.1 and Remark 4.2, printed pp. 14–15 / PDF pp. 16–17

import Mathlib
import Definitions.Def_TightPQRepetition_Main_Oracle

namespace TightPQRepetition.Main

/-- Lemma 4.1 with Remark 4.2 (printed pp. 14–15, PDF pp. 16–17). -/
theorem lemma_4_1 (c L i : ℕ → ℕ) (D : Bool → ℕ → Bits → Bits) (hD : IsSamplerPair c L D)
    (S : (lam : ℕ) → OREICircuit (c lam) (L lam) (i lam)) (hS : IsOracleFamily c L i S)
    (out : (lam : ℕ) → Fin (OREIWires (c lam) (L lam) (i lam)))
    (hout : ∀ lam (b : Fin (c lam)), out lam ≠ Fin.castAdd (i lam) (Fin.castAdd (L lam) (Fin.natAdd 1 b)))
    (φ : (lam : ℕ) → EuclideanSpace ℂ (QAlgorithms.Qubits (i lam)))
    (hφ : ∀ lam, QAlgorithms.IsState (φ lam))
    (p : ℕ → ℕ) (hp : PolyBound p) (hp0 : ∀ lam, 0 < p lam) (Λ : Set ℕ)
    (hadv : ∀ lam ∈ Λ, 1 / (p lam : ℝ) ≤
      |oracleAccept (c lam) (L lam) (i lam) (D false lam) (S lam) (out lam) (φ lam) -
        oracleAccept (c lam) (L lam) (i lam) (D true lam) (S lam) (out lam) (φ lam)|) :
    ∃ T : ℕ → QTest, IsQTestFamily T ∧ ∃ p' : ℕ → ℕ, PolyBound p' ∧ (∀ lam, 0 < p' lam) ∧
      ∀ lam ∈ Λ, 1 / (p' lam : ℝ) ≤
        |avgCoins (c lam) (fun r => (T lam).accept (D false lam r)) -
          avgCoins (c lam) (fun r => (T lam).accept (D true lam r))| := by sorry

end TightPQRepetition.Main
