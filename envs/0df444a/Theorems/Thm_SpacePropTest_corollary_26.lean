-- Prove2me | Theorems.Thm_SpacePropTest_corollary_26
-- name    : SpacePropTest.corollary_26
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:56:38.166619+00:00
-- url     : https://prove2.me/theorems/31dd702b-9667-4330-bc28-6b2fadc6ffdd
-- title:
--   Corollary 26, p.23 — $\mathrm{poly}(n^L,1/\varepsilon)$ edges approximate $\Pr_{i,x}[D_if_\rho^{\le L}(x)\le t]$ within $\varepsilon/(16n^3)$ for every $f$ and $t$
-- statement:
--   There is an absolute constant $C$ such that the following holds. Let $n\ge1$, $\varepsilon\in(0,1]$ and $\rho,L$ as in (5). There is a non-empty multiset $H$ of edges $(x,i)$ with $|H|\le C\,(n^L/\varepsilon)^C$ such that for every $f:\{\pm1\}^n\to\{\pm1\}$ and every $t\in\mathbb R$,
--
--   $$\Bigg|\frac1{|H|}\sum_{(x,i)\in H}\mathbf 1[D_if_\rho^{\le L}(x)\le t]-\Pr_{i,x}[D_if_\rho^{\le L}(x)\le t]\Bigg|\le\frac{\varepsilon}{16n^3}.$$
--
--   This is the edge set the tester of Theorem 15 hard-codes.
--
--   Differences from the source:
--   - encoding: $f:\{\pm1\}^n\to\{\pm1\}$ on $\{\pm1\}^n$ → a Boolean function on $\{0,1\}^n$ (`Fin n → Bool`) read through $\mathrm{false}\mapsto-1$, $\mathrm{true}\mapsto+1$; reason: order-preserving bijection; the same monotone functions, derivatives and Fourier coefficients
--   - encoding: $\Pr_{x\sim\{\pm1\}^n,\,i\sim[n]}[\cdot]$ → the fraction of pairs $(x,i)\in\{0,1\}^n\times[n]$ satisfying the event; reason: $x$ and $i$ are uniform and independent
--   - generalization: $L:=O(\sqrt n\log(n/\varepsilon)/\varepsilon^2)$ such that $\rho\le1-3\log(n/\varepsilon)/L$ (5) → every positive integer $L$ with $\rho\le1-3\ln(n/\varepsilon)/L$; reason: every $L$ the paper allows satisfies this condition, so the statement specializes to the paper's $L$
--   - reading: $\mathrm{poly}(n^L,1/\varepsilon)$ edges; a (multi)set → a non-empty list of length at most $C\,(n^L/\varepsilon)^C$, $C$ absolute and chosen before $n,\varepsilon,L$; reason: standard reading of $\mathrm{poly}$ (bounded by a polynomial; since $n^L/\varepsilon\ge1$, $C\,Y^C$ dominates every polynomial in $Y$); the average needs $H$ non-empty
-- source:
--   Canonne, Chen, Pires, Pitassi, Servedio, The Space Complexity of Property Testing, manuscript of November 2, 2026 (sha256 65850aa6…), Corollary 26, p.23 (PDF 25)

import Mathlib
import Definitions.Def_SpacePropTest_Cube
import Definitions.Def_SpacePropTest_Fourier

set_option autoImplicit false

namespace SpacePropTest

/-- **Corollary 26** (C. Canonne, X. Chen, W. Pires, T. Pitassi, R. A. Servedio, *The Space
Complexity of Property Testing*, manuscript of November 2, 2026, sha256 65850aa6…; p.23 (PDF 25)).
With `ρ, L` as in (5), there is a multiset `H` of `poly(n^L, 1/ε)` edges `(x, i)` such that for
every `f : {±1}ⁿ → {±1}` and every `t ∈ ℝ`,
`|(1/|H|) ∑_{(x,i)∈H} 1[D_i f_ρ^{≤L}(x) ≤ t] − Pr_{i,x}[D_i f_ρ^{≤L}(x) ≤ t]| ≤ ε/(16n³)`.

**Formalization Note.** The multiset is a non-empty list; `poly(n^L, 1/ε)` is `C·(n^L/ε)^C`
with `C` absolute, chosen before `n, ε, L`. -/
theorem corollary_26 : ∃ C : ℕ, ∀ (n : ℕ), 1 ≤ n → ∀ (ε : ℝ), 0 < ε → ε ≤ 1 → ∀ (L : ℕ),
    IsLParam n ε L →
    ∃ H : List (Cube n × Fin n), H ≠ [] ∧
      (H.length : ℝ) ≤ C * ((n : ℝ) ^ L / ε) ^ C ∧
      ∀ (f : BoolFn n) (t : ℝ),
        |(H.countP (fun e => decide
              (deriv e.2 (trunc L (noiseOp (rho n ε) (pmFn f))) e.1 ≤ t)) : ℝ) / H.length -
            edgeProbLe (trunc L (noiseOp (rho n ε) (pmFn f))) t| ≤
          ε / (16 * (n : ℝ) ^ 3) := by sorry

end SpacePropTest
