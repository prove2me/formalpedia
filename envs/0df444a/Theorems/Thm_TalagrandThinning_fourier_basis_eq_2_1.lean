-- Prove2me | Theorems.Thm_TalagrandThinning_fourier_basis_eq_2_1
-- name    : TalagrandThinning.fourier_basis_eq_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:43:58.200483+00:00
-- url     : https://prove2.me/theorems/b7845e01-082d-4058-83ec-b1b0585862cb
-- title:
--   Eq. (2.1) — the $s$-biased Fourier basis, expansion and Parseval
-- statement:
--   Let $0<s<1$ and $N\ge0$. Then:
--
--   1. $\mathbb E_{\mu_s}\phi_s=0$ and $\mathbb E_{\mu_s}\phi_s^2=1$ (one coordinate);
--   2. the $2^N$ functions $\omega^{(s)}_I$, $I\subseteq[N]$, are orthonormal in $L^2(\mu_s)$: $\mathbb E_{\mu_s}[\omega^{(s)}_I\omega^{(s)}_K]=\mathbf 1[I=K]$;
--   3. every real function $f$ on the cube satisfies
--   $$f=\sum_{I\subseteq[N]}\hat f_s(I)\,\omega^{(s)}_I;$$
--   4. (Parseval) $\displaystyle \mathbb E_{\mu_s}f^2=\sum_{I}\hat f_s(I)^2.$
--
--   This is the Fourier layer on which the kernel argument runs: Lemma 3.2 expands $L_jf$ in it and the proof of Theorem 1.2 ends with Parseval.
--
--   **Formalization Note** The one-coordinate expectation of $g$ is $s\,g(1)+(1-s)\,g(0)$. "Orthonormal basis" is stated as orthonormality (2) together with the expansion (3).
--
--   Differences from the source:
--   - encoding: subsets $A\subseteq[N]=\{1,\dots,N\}$, $\cap$, $\subseteq$ → indicator vectors $x:\mathrm{Fin}\,N\to\mathrm{Bool}$ on $\{0,\dots,N-1\}$, $\sqcap$, $\le$; reason: the paper identifies a set with its indicator vector (p.2); relabelling the ground set changes no instance
--   - encoding: expectations $\mathbb E_{\mu_s}$ and laws as random variables → finite weighted sums $\sum_x \mu_s(\{x\})\,f(x)$ and measures on the finite cube; reason: the cube is finite, so expectation is a finite sum; same values
--   - encoding: "For $s\in(0,1)$" (p.3) → explicit hypotheses $0<s$, $s<1$; reason: the paper's own range for $\phi_s$, written as binders; it only excludes parameters for which $\phi_s$ is undefined
--   - encoding: "the $2^N$ functions $\omega^{(s)}_I$ are an orthonormal basis" → orthonormality and the expansion of every $f$; reason: an orthonormal spanning family is an orthonormal basis
-- source:
--   Fang & Wang, A Note on a Result of Chen Li: the Thinning Problem via the Kernel Method, arXiv:2609.18458 (held version dated Sep 12, 2026, sha256 68a0f38d…), §2, eq. (2.1) and the sentence before it, p.3

import Mathlib
import Definitions.Def_TalagrandThinning_fourierCoeff

set_option autoImplicit false

namespace TalagrandThinning

/-- The `s`-biased Fourier basis of the cube, eq. (2.1)
(arXiv:2609.18458, held version dated Sep 12, 2026, sha256 68a0f38d…, §2, eq. (2.1) and the sentence before it, p.3).

For `s ∈ (0,1)`: (1) the one-coordinate identities `E_{µ_s} ϕ_s = 0` and `E_{µ_s} ϕ_s² = 1`;
(2) the `2^N` functions `ω^{(s)}_I` are orthonormal in `L²(µ_s)`; (3) every real `f` on the cube
equals `∑_{I⊆[N]} f̂_s(I) ω^{(s)}_I`; (4) Parseval, `E_{µ_s} f² = ∑_I f̂_s(I)²`.

**Formalization Note** One-coordinate expectations are `s · ϕ_s(1) + (1 − s) · ϕ_s(0)`; `E_{µ_s}`
is the finite weighted sum `expect s`. Orthonormality plus the expansion (3) is the statement that
the `ω^{(s)}_I` form an orthonormal basis. -/
theorem fourier_basis_eq_2_1 {N : ℕ} (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    (s * phi s true + (1 - s) * phi s false = 0) ∧
    (s * phi s true ^ 2 + (1 - s) * phi s false ^ 2 = 1) ∧
    (∀ I K : Finset (Fin N),
      expect s (fun x : Cube N => omega s I x * omega s K x) = if I = K then 1 else 0) ∧
    (∀ (f : Cube N → ℝ) (x : Cube N),
      f x = ∑ I : Finset (Fin N), fourierCoeff s f I * omega s I x) ∧
    (∀ f : Cube N → ℝ,
      expect s (fun x => f x ^ 2) = ∑ I : Finset (Fin N), fourierCoeff s f I ^ 2) := by sorry

end TalagrandThinning
