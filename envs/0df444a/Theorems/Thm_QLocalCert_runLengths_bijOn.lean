-- Prove2me | Theorems.Thm_QLocalCert_runLengths_bijOn
-- name    : QLocalCert.runLengths_bijOn
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:40:34.020899+00:00
-- url     : https://prove2.me/theorems/bf5edcc6-9e2f-4431-99dd-1c449b984776
-- title:
--   The run-length map $z\mapsto r(z)$ is a bijection from balanced strings onto vectors summing to $N/2$
-- statement:
--   For every even $N$, the map $z\mapsto r(z)$ is a bijection between the balanced strings $z\in\{0,1\}^N$ (Hamming weight $N/2$) and the vectors $(r_0,\dots,r_{N/2})\in\mathbb Z_{\ge0}^{N/2+1}$ with
--   $$
--   \sum_{i=0}^{N/2}r_i=\frac N2 .
--   $$
--
--   It lets each side of $T^{\mathrm{tr}}_{N,\mu}(z,z')$ encode its string without loss: the root $h_L$ reconstructs $z$ from the run lengths of its gadgets (Lemmas 26–28).
--
--   Differences from the source:
--   - generalization: even N ≥ 8 (the standing assumption of §4) → every even N; reason: the bijection holds for every even N and specializes to N ≥ 8
-- source:
--   Jauregui, Miyamoto, Quantum Advantage in Local Certification of Graph Properties, STOC 2027 submission (manuscript sha256 b707143b1ab5511bef4c2b77e1b803f28b32cced25a008516898fd11d28c0451), §4, display defining r(z), p.34

import Mathlib
import Definitions.Def_QLocalCert_runLengths

set_option autoImplicit false

namespace QLocalCert

/-- **The run-length bijection** (§4, display defining r(z), p.34). "We encode strings z ∈ {0, 1}^N
of Hamming weight N/2 by their zero-run lengths. … This is a bijection between balanced N-bit
strings and vectors in Z_{≥0}^{N/2+1} summing to N/2."

Source: B. Jauregui, M. Miyamoto, *Quantum Advantage in Local Certification of Graph Properties*,
STOC 2027 submission (manuscript sha256 b707143b…0c51), §4, p.34.

**Formalization Note.** Stated for every even `N` (the paper's context is even `N ≥ 8`;
generalization). `Set.BijOn` says `r` maps balanced strings into, injectively and onto, the
vectors `(r₀, …, r_{N/2}) ∈ ℕ^{N/2+1}` with `∑ rᵢ = N/2`. -/
theorem runLengths_bijOn (N : ℕ) (hN : Even N) :
    Set.BijOn runLengths {z : Fin N → Bool | Balanced z}
      {r : Fin (N / 2 + 1) → ℕ | ∑ i, r i = N / 2} := by sorry

end QLocalCert
