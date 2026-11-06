-- Prove2me | Theorems.Thm_ReserveLB_certificate_6_1
-- name    : ReserveLB.certificate_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:35:13.285319+00:00
-- url     : https://prove2.me/theorems/f1207089-330d-486e-a9b5-84d4c8a5abac
-- title:
--   Section 6.1 — every infeasible target $L$ certifies $\mathrm{OPT}_k > 9L/40$
-- statement:
--   Let $m \ge 1$ machines have speeds $s_i > 0$, let $1 \le k \le m$, and let the sizes $X_1, \dots, X_n$ be independent with listed laws. Let virtual classes with speeds $S_h > 0$ satisfy (1), and let a forward map $F$ from original to virtual machines satisfy
--   $$
--   T_{F(\sigma)}(x) \le 4\,T_\sigma(x)
--   $$
--   for every reservation $\sigma$ with nonempty sets and every size vector $x \ge 0$ (the loss-four clause of Lemma 2.2). If, for some $L > 0$, the system $\mathcal F_k(L)$ has no integral feasible point, then
--   $$
--   \mathrm{OPT}_k > \tfrac{9}{40}\,L .
--   $$
--
--   Each infeasible target of the bisection is therefore a certificate, and $\mathrm{LB}_k = \max\{L_0, 9L/40\}$ is a valid lower bound.
--
--   Differences from the source:
--   - generalization: an infeasible target: the rational LP F_k(L) with lower enclosures has no feasible point → F_k(L) with the true coefficients has no integral feasible point; reason: LP infeasibility excludes integral points with the lower coefficients, hence with the larger true coefficients; the hypothesis is weaker
--   - generalization: rational speeds; the classes and F constructed by Lemma 2.2 → real positive speeds; any classes with positive speeds satisfying (1) and any forward map with loss four; reason: the argument uses only these properties of Lemma 2.2 (with Lemma 3.1); Lemma 2.2's output has them
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Section 6.1, p.12

import Mathlib
import Definitions.Def_ReserveLB_LawOK
import Definitions.Def_ReserveLB_Tsig
import Definitions.Def_ReserveLB_OPTk
import Definitions.Def_ReserveLB_ClassStr
import Definitions.Def_ReserveLB_ClassStr_VM
import Definitions.Def_ReserveLB_ClassStr_vspeed
import Definitions.Def_ReserveLB_ClassStr_Smooth1
import Definitions.Def_ReserveLB_Pattern
import Definitions.Def_ReserveLB_coefMu
import Definitions.Def_ReserveLB_coefV
import Definitions.Def_ReserveLB_coefW
import Definitions.Def_ReserveLB_coefC
import Definitions.Def_ReserveLB_Feasible

namespace ReserveLB

/-- **Section 6.1 — every infeasible target certifies `OPT_k > 9L/40`.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Section 6.1, p.12: "Otherwise retain an infeasible L and feasible U = 2L. By lemmas 3.1 and
2.2, every infeasible target separately certifies OPTk > 9L/40."

Let `m ≥ 1` machines have positive speeds, `1 ≤ k ≤ m`, and let `n` jobs be independent with
listed laws. Let virtual classes satisfy (1) with positive speeds, and let a forward map `F` from
originals to virtual machines lose at most a factor four on every reservation and every size
vector (Lemma 2.2). If `F_k(L)`, `L > 0`, has no integral feasible point, then `OPT_k > 9L/40`.

**Formalization Note.** "Infeasible" is read with the true coefficients and integral points: an
infeasible lower-enclosure LP has no integral point with lower coefficients, hence none with the
larger true ones. Speeds are real. -/
theorem certificate_6_1 {m n : ℕ} (hm : 1 ≤ m) (s : Fin m → ℝ) (hs : ∀ i, 0 < s i) (k : ℕ)
    (hk : 1 ≤ k) (hkm : k ≤ m) (law : Fin n → List (ℚ × ℚ)) (hlaw : ∀ j, LawOK (law j))
    (C : ClassStr) (hS : ∀ h, 0 < C.S h) (hC : C.Smooth1) (F : Fin m → C.VM)
    (hF : ∀ σ : Fin n → Finset (Fin m), (∀ j, (σ j).Nonempty) → ∀ x : Fin n → ℝ, (∀ j, 0 ≤ x j) →
      Tsig C.vspeed (fun j => (σ j).image F) x ≤ 4 * Tsig s σ x)
    (L : ℝ) (hL : 0 < L)
    (hinf : ¬ ∃ qs : Fin n → Pattern C k,
      Feasible C k n (fun j q h => coefMu C L (law j) q.1 h) (fun j q => coefV C L (law j) q.1)
        (fun j q r h => coefW C L (law j) q.1 r h) (fun j q => coefC C L (law j) q.1)
        (fun j q => if q = qs j then 1 else 0)) :
    9 * L / 40 < OPTk k s law := by sorry

end ReserveLB
