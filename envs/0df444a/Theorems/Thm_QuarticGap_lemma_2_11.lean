-- Prove2me | Theorems.Thm_QuarticGap_lemma_2_11
-- name    : QuarticGap.lemma_2_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:46:42.104344+00:00
-- url     : https://prove2.me/theorems/6adcc564-758c-4310-b51c-544e885b0f82
-- title:
--   Lemma 2.11 — the sign matrices $W(\emptyset)$, $W(a)$ and access to them through the bit oracle of $s$
-- statement:
--   Let $W(\emptyset) = \sqrt n H$, so that $R = H$. For $a \in \{0,1\}^k \setminus \{0^k\}$, let $W(a)$ be the sign matrix for which $R = W(a)/\sqrt n$ equals $H$ except that row $a$ is replaced by $u^{\mathsf T}$.
--
--   1. These matrices satisfy the promise. For $W(\emptyset)$, $v = e_0$. For $W(a)$,
--   $$
--   \|R\| = \sqrt 2, \qquad v = e_0+e_a, \qquad RR^{\mathsf T}v = 2v .
--   $$
--   2. Index the strings $s \in \{0,1\}^{n-1}$ by $\{0,1\}^k \setminus \{0^k\}$, and put $W(s) = W(\emptyset)$ for $s = 0$ and $W(s) = W(a)$ when $s$ is the indicator vector of $a$. For every family with known magnitudes in $f(a,b) = W_{ab}$, every coherent input operation on the inputs with $W = W(s)$ can be implemented with $O(1)$ queries to the bit oracle of $s$.
--
--   These are the hard instances of the quantum lower bound.
--
--   **Formalization Note** $s$ is written on all of $\{0,1\}^k$ with $s_{0^k} = 0$. The constant is absolute and the circuits are fixed before $s$.
--
--   Differences from the source:
--   - encoding: n a power of four, indices {0,1}^k → n = 4^ℓ, k = 2ℓ, √n = 2^ℓ; reason: the same values of n
--   - generalization: a family whose map (i, j) ↦ σ_ij is computed by a fixed reversible circuit → no such hypothesis; reason: the Lean circuits may use any unitary gate, so the map is one gate; every family of the source is covered
--   - encoding: matrices of size N₁ × N₂ → matrices indexed by d₁ and d₂ qubit registers; reason: any size fits on ⌈log N⌉ wires with zero rows and columns added
--   - encoding: Definition 2.2 is for a nonzero matrix → the hypothesis A f ≠ 0 for every f; reason: the standing assumption of Definition 2.2; for A = 0 norm preparation has no target state
--   - encoding: strings s ∈ {0,1}^{n−1} indexed by {0,1}^k ∖ {0^k} → strings on {0,1}^k with s at 0^k equal to 0; reason: the bit oracle of such a string at 0^k returns 0, so it is the same oracle with one fixed position added
-- source:
--   Chakrabarti, Herman, Kim, Ozgul, The Quartic Gap Between Quantum and Dequantized Algorithms for Linear Algebra Is Tight, arXiv:2610.42069 (file sha256 9f68aaf9…), Lemma 2.11, p.20

import Mathlib
import Definitions.Def_QuarticGap_Ahat

open QAlgorithms

namespace QuarticGap

/-- Lemma 2.11 (arXiv:2610.42069 (file sha256 9f68aaf9…), p.20). `W(∅)` has `R = H`, and `W(a)`, for
`a ≠ 0^k`, has `R` equal to `H` except that row `a` is replaced by `uᵀ`. These satisfy the promise (2).
For `W(∅)`, `v = e₀`. For `W(a)`, `∥R∥ = √2`, `v = e₀ + e_a`, `RRᵀv = 2v`. For every family with known
magnitudes in `f(a, b) = W_ab`, every coherent input operation on the inputs with `W = W(s)` can be
implemented with `O(1)` queries to the bit oracle of `s`.

**Formalization Note** `W(s)` is `hardW s`, with `s` the zero string or the indicator of `a ≠ 0^k`.
`s` is on all of `{0,1}^k`, with `s_{0^k} = 0`, which is the source's string indexed by
`{0,1}^k ∖ {0^k}`. The constant is absolute and the circuits are fixed before `s`. -/
theorem lemma_2_11 :
    (∀ ℓ : ℕ,
      Rmat (hardW (ℓ := ℓ) fun _ => false) = Hmat ℓ ∧
      hardW (ℓ := ℓ) (fun _ => false) ∈ G ℓ ∧
      vVec (hardW (ℓ := ℓ) fun _ => false) = eVec (zeros _) ∧
      ∀ a : Bits ℓ, a ≠ zeros _ →
        (∀ r b, Rmat (hardW fun x => decide (x = a)) r b =
          if r = a then uVec ℓ b else Hmat ℓ r b) ∧
        hardW (fun x => decide (x = a)) ∈ G ℓ ∧
        specNorm (Rmat (hardW fun x => decide (x = a))) = Real.sqrt 2 ∧
        vVec (hardW fun x => decide (x = a)) = eVec (zeros _) + eVec a ∧
        (Rmat (hardW fun x => decide (x = a)) *
            (Rmat (hardW fun x => decide (x = a))).transpose).mulVec
          (vVec (hardW fun x => decide (x = a))) =
          (2 : ℝ) • vVec (hardW fun x => decide (x = a)))  ∧
    (∃ C : ℕ, ∀ (ℓ d₁ d₂ w : ℕ)
      (A : (Qubits (2 * ℓ + 2 * ℓ) → ℤˣ) → Matrix (Qubits d₁) (Qubits d₂) ℝ),
      IsKnownMagnitudeFamily A → (∀ f, A f ≠ 0) → ∀ enc : ℝ → Qubits w,
      ∃ (N : ℕ) (sim : AccessSim (coherentArity d₁ d₂ w) (2 * ℓ + 1) N), sim.CallsAtMost C ∧
        ∀ s : Bits ℓ → Bool,
          (s = (fun _ => false) ∨ ∃ a : Bits ℓ, a ≠ zeros _ ∧ s = fun x => decide (x = a)) →
          ∃ orc, IsCoherentAccess (A (flatSign (hardW s)))
              (fun i j => enc (A (flatSign (hardW s)) i j)) orc ∧
            sim.Realizes (bitOracle s) orc) := by sorry

end QuarticGap
