-- Prove2me | Theorems.Thm_QLocalCert_lemma_9
-- name    : QLocalCert.lemma_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:41:43.688202+00:00
-- url     : https://prove2.me/theorems/fb0c8747-3ad5-407d-a318-fcd9e1b3d171
-- title:
--   Lemma 9 — one repetition of Protocol 1 accepts a no-instance with probability at most $1-\frac{1}{70(r+1)}$
-- statement:
--   Let $r\ge1$ and let $|h_x\rangle,|h_y\rangle$ be unit vectors in $\mathbb C^{2^\ell}$ with $|\langle h_x|h_y\rangle|^2\le\tfrac12$ (as for fingerprints of distinct strings $x\ne y$). Let $M$ be the accepting effect of one repetition of Protocol 1 on the path $v_0,\dots,v_r$, averaged over its coins. Then for every finite environment $\mathsf E$ and every density operator $\rho$ on the blocks of the repetition together with $\mathsf E$ (arbitrarily entangled internally and with $\mathsf E$),
--   $$
--   \operatorname{tr}\big[(M\otimes I_{\mathsf E})\rho\big]\le1-\gamma,\qquad\gamma=\frac{1}{70(r+1)} .
--   $$
--
--   The rejection probability $\Omega(1/r)$ per repetition, instead of the earlier $\Omega(1/r^2)$, is what brings the equality protocol to $O(r\log N)$ qubits (Lemma 10) and the constant of Theorem 1 independent of $\mu$.
--
--   Differences from the source:
--   - generalization: x ≠ y (distinct strings with their fingerprints) → any unit vectors h_x, h_y with |⟨h_x|h_y⟩|² ≤ 1/2; reason: the proof uses x ≠ y only through this overlap bound (p.19); fingerprints of distinct strings satisfy it (p.15)
--   - encoding: probability that all tests of repetition k accept, for a state entangled internally and with the rest of the proof → tr[(M ⊗ I_E) ρ] for every finite E and density operator ρ, M = rep1Effect averaged over the coins; reason: this is the operator form used in the proof of Lemma 10, p.21
-- source:
--   Jauregui, Miyamoto, Quantum Advantage in Local Certification of Graph Properties, STOC 2027 submission (manuscript sha256 b707143b1ab5511bef4c2b77e1b803f28b32cced25a008516898fd11d28c0451), Lemma 9, pp.18–21, for Protocol 1, p.17

import Mathlib
import Definitions.Def_QLocalCert_rep1Effect
import Definitions.Def_WildeQIT_IsDensityOperator

open Matrix
open scoped ComplexOrder Kronecker
set_option autoImplicit false

namespace QLocalCert

/-- **Lemma 9** (Soundness of a single repetition, p.18). "Suppose x ≠ y. Then for every state of
the blocks of a fixed repetition k ∈ [m], arbitrarily entangled internally and with the rest of the
proof, the probability that all tests of repetition k accept is at most 1 − γ, where
γ := 1/(70(r+1))."

Source: B. Jauregui, M. Miyamoto, *Quantum Advantage in Local Certification of Graph Properties*,
STOC 2027 submission (manuscript sha256 b707143b…0c51), Lemma 9, p.18, for Protocol 1, p.17, on a path `v₀, …, v_r`, `r ≥ 1`.

**Formalization Note.**
* "The probability that all tests of repetition k accept" is `tr[(M ⊗ I_E) ρ]` for the effect
  `M = rep1Effect h_x h_y r` of the repetition averaged over its coins (as in the proof of Lemma 10,
  p.21), where `ρ` is any density operator on the blocks of the repetition and an arbitrary finite
  environment `E` (the rest of the proof and any purifying system).
* `x ≠ y` enters only through the fingerprint overlap: the statement assumes unit vectors
  `h_x, h_y` with `|⟨h_x|h_y⟩|² ≤ 1/2` (generalization; distinct fingerprints satisfy it, p.15). -/
theorem lemma_9 (r ℓ : ℕ) (hr : 1 ≤ r) (hx hy : Qb ℓ → ℂ)
    (hx1 : star hx ⬝ᵥ hx = 1) (hy1 : star hy ⬝ᵥ hy = 1) (hxy : ‖star hx ⬝ᵥ hy‖ ^ 2 ≤ 1 / 2)
    (E : Type) [Fintype E] [DecidableEq E] (ρ : Matrix (Blk r ℓ × E) (Blk r ℓ × E) ℂ)
    (hρ : WildeQIT.IsDensityOperator ρ) :
    (trace ((rep1Effect hx hy r ⊗ₖ (1 : Matrix E E ℂ)) * ρ)).re ≤
      1 - 1 / (70 * ((r : ℝ) + 1)) := by sorry

end QLocalCert
