-- Prove2me | Theorems.Thm_QuantumLTF_Membership_Supplement_hermite_band_bounds_53
-- name    : QuantumLTF.Membership.Supplement.hermite_band_bounds_53
-- status  : Proved
-- author  : @Robin Kothari
-- created : 2026-11-24T07:31:06.974306+00:00
-- url     : https://prove2.me/theorems/dd02fcff-fdea-4eac-bd7c-aaf3edfe0a62
-- title:
--   Hermite degree-band mass bounds, rotational invariance, and band-slice approximation
-- statement:
--   Let $\gamma_n$ denote the standard Gaussian measure on $\mathbb{R}^n$, and for any unit vector $w \in \mathbb{S}^{n-1}$ let $f_w(x) = \mathrm{sign}(\langle w, x \rangle)$ have normalized multivariate probabilists' Hermite coefficients $\widehat{f_w}(\alpha) = \int_{\mathbb{R}^n} f_w(x) h_\alpha(x)\, d\gamma_n(x)$ for $\alpha \in \mathbb{N}^n$. For $K \in \mathbb{N}$, write $B_K = \{K, K+1, \dots, 2K\}$ for the Hermite degree band, let $p_K(w) = \sum_{K \le |\alpha| \le 2K} \widehat{f_w}(\alpha)^2$ (`bandWeight w K`), and let $p_K = p_K(e_0)$ (`p1D53 K`) denote the one-dimensional band weight.
--
--   This theorem establishes four structural properties of Hermite degree-band states and projections:
--
--   1. **Universal band-mass bounds and rotational invariance:** There exists a universal constant $c_{\mathrm{band}} > 0$ such that for every $K \ge 1$,
--   $$
--   \frac{c_{\mathrm{band}}}{\sqrt{K}} \le p_K \le 1,
--   $$
--   and for every $n, K \in \mathbb{N}$ and every unit vector $w \in \mathbb{S}^{n-1}$, the multivariate degree-band mass is rotation-invariant:
--   $$
--   \sum_{K \le |\alpha| \le 2K} \widehat{f_w}(\alpha)^2 = p_K.
--   $$
--
--   2. **Band-state normalization and projected error transfer:** For all $n, K, D, q, a \in \mathbb{N}$ satisfying $1 \le K$ and $2K + 1 \le D \le 2^q$, every unit vector $w \in \mathbb{S}^{n-1}$, and every $(nq+a)$-qubit vector $F_w \in \mathbb{C}^{2^{nq+a}}$, the ideal band state $|F_w^{B_K}\rangle$ (`bandKet n q K w`) has unit norm $\| |F_w^{B_K}\rangle \| = 1$, and the unnormalized degree-band slice $\Pi_{B_K} F_w$ (`bandSlice53 n q a K Fw`) satisfies
--   $$
--   \bigl\| \Pi_{B_K} F_w - \sqrt{p_K(w)}\, |F_w^{B_K}\rangle \bigr\| \le \bigl\| P_D^{\otimes n} F_w - P_D^{\otimes n} |F_w\rangle \bigr\|,
--   $$
--   where the right-hand side is `projDist n q a D w Fw`.
--
--   3. **Coordinate-wise evaluation of `bandSlice53`:** Whenever $2K + 1 \le 2^q$, the amplitude of `bandSlice53 n q a K F` at any $nq$-qubit basis string $z$ equals $F(z, 0^a)$ if the sum of the $n$ decoded $q$-bit register integers lies in $[K, 2K]$, and $0$ otherwise.
--
--   4. **Decoding equivalence:** Whenever $2K + 1 \le D \le 2^q$, an $nq$-qubit string $z$ has decoded register sum in $[K, 2K]$ if and only if $z$ is the most-significant-bit binary encoding of some $\alpha \in [D]^n$ with $K \le |\alpha| \le 2K$.
--
--   These results encapsulate the analytic Gaussian Hermite geometry and degree-band projection estimates required for the high-degree projection algorithm of Theorem 5.3.
--
--   **Formalization Note** Degree registers use `Qubits (n * q)` with most-significant-bit encoding `natToBits q` and decoding `bitsToNat` via `flatReg` and `splitReg`.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Lemma 2.3 (p. 20, PDF p. 21) and Section 5.2, Eqs. (167)-(173) and Theorem 5.3 (pp. 63-64, PDF pp. 64-65).

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53

set_option autoImplicit false

namespace QuantumLTF.Membership.Supplement

open QAlgorithms QuantumLTF.Membership

theorem hermite_band_bounds_53 :
    (∃ c_band : ℝ, 0 < c_band ∧
      (∀ K : ℕ, 1 ≤ K → c_band / Real.sqrt K ≤ p1D53 K ∧ p1D53 K ≤ 1) ∧
      (∀ (n K : ℕ) (w : EuclideanSpace ℝ (Fin n)), ‖w‖ = 1 → bandWeight w K = p1D53 K)) ∧
    (∀ (n K D q a : ℕ), 1 ≤ K → 2 * K + 1 ≤ D → D ≤ 2 ^ q →
      ∀ (w : EuclideanSpace ℝ (Fin n)), ‖w‖ = 1 →
      ∀ (Fw : EuclideanSpace ℂ (Qubits (n * q + a))),
        ‖bandKet n q K w‖ = 1 ∧
        ‖bandSlice53 n q a K Fw - (Real.sqrt (bandWeight w K) : ℂ) • bandKet n q K w‖ ≤
          projDist n q a D w Fw) ∧
    (∀ (n q a K : ℕ), 2 * K + 1 ≤ 2 ^ q →
      ∀ (F : EuclideanSpace ℂ (Qubits (n * q + a))) (z : Qubits (n * q)),
        bandSlice53 n q a K F z =
          if K ≤ ∑ i : Fin n, bitsToNat (splitReg n q z i) ∧
              ∑ i : Fin n, bitsToNat (splitReg n q z i) ≤ 2 * K
          then F (Fin.append z (fun _ : Fin a => false))
          else 0) ∧
    (∀ (n q D K : ℕ), 2 * K + 1 ≤ D → D ≤ 2 ^ q →
      ∀ z : Qubits (n * q),
        (K ≤ ∑ i : Fin n, bitsToNat (splitReg n q z i) ∧
            ∑ i : Fin n, bitsToNat (splitReg n q z i) ≤ 2 * K) ↔
          ∃ α : Fin n → Fin D, z = flatReg n q (fun i => natToBits q (α i)) ∧
            K ≤ ∑ i, (α i : ℕ) ∧ ∑ i, (α i : ℕ) ≤ 2 * K) := by sorry

end QuantumLTF.Membership.Supplement
