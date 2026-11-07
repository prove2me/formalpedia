-- Prove2me | Theorems.Thm_QLocalCert_lemma_10
-- name    : QLocalCert.lemma_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:41:35.450786+00:00
-- url     : https://prove2.me/theorems/668dcc94-fa35-4872-9728-6d6ad1c40b0a
-- title:
--   Lemma 10 — $m=\lceil70(r+1)\ln3\rceil$ repetitions: perfect completeness, soundness $1/3$, $O(r\log N)$ qubits
-- statement:
--   There is a constant $C$ such that for every $N\ge2$ there are $\ell$ and fingerprints $X\mapsto|h_X\rangle\in\mathbb C^{2^\ell}$ (unit vectors with $|\langle h_X|h_Y\rangle|^2\le\tfrac12$ for $X\ne Y$) with the following properties for every path length $r\ge1$. Let $m=\lceil70(r+1)\ln3\rceil$ and let $M_{x,y}=\bigotimes_{k=1}^m M_k$ be the accepting effect of $m$ independent repetitions of Protocol 1 with inputs $x,y$.
--   1. **Perfect completeness:** for every $x$, the honest certificate $|h_x\rangle$ in every block is accepted with probability $1$ on input $(x,x)$.
--   2. **Soundness:** for $x\ne y$ and every density operator $\rho$ on the blocks of all $m$ repetitions (arbitrarily entangled),
--   $$
--   \operatorname{tr}(M_{x,y}\,\rho)\le\tfrac13 .
--   $$
--   3. **Size:** the $2m\ell$ proof qubits and the $m\ell$ message qubits per node are each at most $C\,r\log_2N$.
--
--   This is the $O(r\log N)$ bound of Theorem 5, the equality protocol run on the central path in Lemma 28.
--
--   Differences from the source:
--   - encoding: the protocol on a path with inputs x, y → its joint accepting effect mEffect (h x) (h y) r m and the honest vector |h_x⟩^{⊗(2r+1)m}; reason: acceptance of a certificate state is the trace against this effect
--   - encoding: O(r log N) qubits of proof and of messages per node → 2mℓ ≤ C r log₂ N and mℓ ≤ C r log₂ N with C before N and r, for N ≥ 2, r ≥ 1; reason: big-O as one constant; the qubit counts are those of Protocol 1, p.17
-- source:
--   Jauregui, Miyamoto, Quantum Advantage in Local Certification of Graph Properties, STOC 2027 submission (manuscript sha256 b707143b1ab5511bef4c2b77e1b803f28b32cced25a008516898fd11d28c0451), Lemma 10, p.21; Protocol 1, p.17

import Mathlib
import Definitions.Def_QLocalCert_rep1Effect
import Definitions.Def_WildeQIT_IsDensityOperator

open Matrix
open scoped ComplexOrder
set_option autoImplicit false

namespace QLocalCert

/-- **Lemma 10** (p.21). "With m := ⌈70(r + 1) ln 3⌉ = Θ(r) repetitions, the protocol has perfect
completeness and soundness error at most 1/3 against arbitrary entangled certificates, with
O(r log N) qubits of proof and of messages per node."

Source: B. Jauregui, M. Miyamoto, *Quantum Advantage in Local Certification of Graph Properties*,
STOC 2027 submission (manuscript sha256 b707143b…0c51), Lemma 10, p.21, for Protocol 1, p.17 ("Per node this uses 2mℓ proof qubits and mℓ
message qubits, where m is the repetition parameter and ℓ is the size of the fingerprints").

**Formalization Note.**
* The fingerprints are a family `h : {0,1}^N → ℂ^{2^ℓ}` of unit vectors with
  `|⟨h_X|h_Y⟩|² ≤ 1/2` for `X ≠ Y` (§2, p.15), chosen for `N` before `r`.
* The protocol on the path `v₀, …, v_r` (`r ≥ 1`) with inputs `x, y` is represented by its joint
  accepting effect `⊗_{k=1}^m M_k = mEffect (h x) (h y) r m`, averaged over all coins.
  (i) Perfect completeness: on `x = y` the honest certificate `|h_x⟩` in every block is accepted
  with probability 1. (ii) Soundness: for `x ≠ y` every density operator on the `m` repetitions'
  blocks (arbitrarily entangled) is accepted with probability at most 1/3. (iii) `O(r log N)` is
  one constant `C` before `N` and `r`, applied to the `2mℓ` proof qubits and the `mℓ` message
  qubits per node. `ln` is `Real.log`, `log` is `Real.logb 2`. -/
theorem lemma_10 :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N → ∃ ℓ : ℕ, ∃ h : (Fin N → Bool) → Qb ℓ → ℂ,
      (∀ X, star (h X) ⬝ᵥ h X = 1) ∧ (∀ X Y, X ≠ Y → ‖star (h X) ⬝ᵥ h Y‖ ^ 2 ≤ 1 / 2) ∧
      ∀ r : ℕ, 1 ≤ r →
        let m : ℕ := ⌈70 * ((r : ℝ) + 1) * Real.log 3⌉₊
        (∀ X, (trace (mEffect (h X) (h X) r m *
            vecMulVec (honestVec (h X) r m) (star (honestVec (h X) r m)))).re = 1) ∧
        (∀ X Y, X ≠ Y → ∀ ρ : Matrix (Fin m → Blk r ℓ) (Fin m → Blk r ℓ) ℂ,
            WildeQIT.IsDensityOperator ρ → (trace (mEffect (h X) (h Y) r m * ρ)).re ≤ 1 / 3) ∧
        ((2 * m * ℓ : ℕ) : ℝ) ≤ C * r * Real.logb 2 N ∧
        ((m * ℓ : ℕ) : ℝ) ≤ C * r * Real.logb 2 N := by sorry

end QLocalCert
