-- Prove2me | Theorems.Thm_TimeSpaceMA_parameter_bounds
-- name    : TimeSpaceMA.parameter_bounds
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:57:27.20865+00:00
-- url     : https://prove2.me/theorems/a9379a24-7ecd-463e-9331-a9caf66d4c37
-- title:
--   (3), (4) and the §3.7 exponent bounds
-- statement:
--   Let $T,S\ge1$ and $S^2\le N$ be real, $H=N^{1/2}$, $E=\max\{N,T^{3/4}N^{1/8}S^{1/2},T^{1/3}N^{2/3}S^{1/6}\}<T$, and set $K=E/S$, $B=TS/E$, $A=T/E$, $C=E^3/(T^2S^2)$, $D=AC$. Then:
--
--   1. (3): $KS=E$, $DBS=E$, $ACBS=E$, $K^2/(AD)=E$, $BHK/C\le E$, $ABH\le E$, $N\le E$;
--   2. (4): $E\ge(T^{3/4}N^{1/8}S^{1/2})^{4/5}(T^{1/3}N^{2/3}S^{1/6})^{1/5}=T^{2/3}N^{7/30}S^{13/30}$;
--   3. (p.21) $A\ge1$, $CBS\le E$, $BH\le E$; if $AB\le H$ then $N(AB)^{1/4}\le E$; if $AB\ge H$ then $ABN^{5/8}\le E$;
--   4. (p.22) $B\le T^{1/4}S^{1/2}N^{-1/8}\le T^{1/4}S^{1/4}$, and for $\omega'\ge0$, $THB^{\omega'}\le T^{1+\omega'/4}HS^{\omega'/4}$.
--
--   These inequalities are what the choice of parameters achieves.
--
--   Differences from the source:
--   - encoding: K, B, A, C, D rounded to integers (Remark 3.1) → the real values before rounding; reason: (3) is stated "up to a factor" after rounding; on p.19 it is the identity of real parameters
--   - generalization: ω − 2 + ε with ε ≤ 3/4 on p.22 → any real ω′ ≥ 0; reason: the inequality uses only that the exponent is nonnegative
--   - encoding: S ≤ H, with H the power of 2 of §3.1 → S² ≤ N, H = N^{1/2}; reason: the condition used on p.22 ("S ≤ N^{1/2}"), and N = H² on p.7
-- source:
--   Williams, Xi, Short Non-Interactive Proofs for Time-Space Computations, STOC 2027 submission (manuscript sha256 184c2f95…), (3), (4), §3.7, p.19; §3.7, Arthur's running time, p.21; §3.7, Total running time, p.22; parameters, §3.1, p.8

import Definitions.Def_TimeSpaceMA_timeSpaceE

namespace TimeSpaceMA

/-- **(3), (4) and the exponent bounds of §3.7** (Williams, Xi, STOC 2027 submission, manuscript sha256
184c2f95…, pp.19, 21, 22). The parameters `K = E/S`, `B = TS/E`, `A = T/E`, `C = E³/(T²S²)`, `D = AC` of §3.1,
p.8, satisfy the identities and inequalities (3), the bound (4), `A ≥ 1`, the two cases of p.21, and the bounds
on `B` of p.22.

**Formalization Note** Real `T, S ≥ 1`, `S² ≤ N` (from `S ≤ H = N^{1/2}`), `E < T`, as on pp.7–8. The parameters
are real numbers, before the rounding of Remark 3.1. `ω′ = ω − 2 + ε` on p.22; any `ω′ ≥ 0` is covered. -/
theorem parameter_bounds (T N S : ℝ) (hT : 1 ≤ T) (hS : 1 ≤ S) (hN : S ^ 2 ≤ N)
    (hE : timeSpaceE T N S < T) :
    let E := timeSpaceE T N S
    let H := N ^ (1 / 2 : ℝ)
    let K := E / S
    let B := T * S / E
    let A := T / E
    let C := E ^ 3 / (T ^ 2 * S ^ 2)
    let D := A * C
    K * S = E ∧ D * B * S = E ∧ A * C * B * S = E ∧ K ^ 2 / (A * D) = E ∧ B * H * K / C ≤ E ∧
      A * B * H ≤ E ∧ N ≤ E ∧
      (T ^ (3 / 4 : ℝ) * N ^ (1 / 8 : ℝ) * S ^ (1 / 2 : ℝ)) ^ (4 / 5 : ℝ) *
          (T ^ (1 / 3 : ℝ) * N ^ (2 / 3 : ℝ) * S ^ (1 / 6 : ℝ)) ^ (1 / 5 : ℝ) =
        T ^ (2 / 3 : ℝ) * N ^ (7 / 30 : ℝ) * S ^ (13 / 30 : ℝ) ∧
      T ^ (2 / 3 : ℝ) * N ^ (7 / 30 : ℝ) * S ^ (13 / 30 : ℝ) ≤ E ∧
      1 ≤ A ∧ C * B * S ≤ E ∧ B * H ≤ E ∧
      (A * B ≤ H → N * (A * B) ^ (1 / 4 : ℝ) ≤ E) ∧
      (H ≤ A * B → A * B * N ^ (5 / 8 : ℝ) ≤ E) ∧
      B ≤ T ^ (1 / 4 : ℝ) * S ^ (1 / 2 : ℝ) * N ^ (-(1 / 8) : ℝ) ∧
      T ^ (1 / 4 : ℝ) * S ^ (1 / 2 : ℝ) * N ^ (-(1 / 8) : ℝ) ≤ T ^ (1 / 4 : ℝ) * S ^ (1 / 4 : ℝ) ∧
      ∀ ω' : ℝ, 0 ≤ ω' →
        T * H * B ^ ω' ≤ T ^ (1 + ω' / 4) * H * S ^ (ω' / 4) := by sorry

end TimeSpaceMA
