-- Prove2me | Theorems.Thm_PreservePast_Supplement_theorem_20
-- name    : PreservePast.Supplement.theorem_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:43:16.796078+00:00
-- url     : https://prove2.me/theorems/494b6534-85bd-43db-8caf-01f0d638c145
-- title:
--   Theorem 20 — spectral-energy response law
-- statement:
--   Histories are the matrices $Z\in\mathbb R^{K\times d}$ with $\|Z\|_{\mathrm{op}}\le1$, $\|Z\|_F^2\le E$; a query reveals $L\in\mathbb R^{m\times K}$ with $\|L\|_F\le1$, and the response must have rank at most $r$, norm at most one, and excess at most $\alpha$ over the best such approximation of $LZ$, with probability $1-\delta$ for each fixed history and query. Let $B^\ast$ be the least register width. Fix $0<\delta<1/2$. For $d\ge2$, $1\le E\le K\le d$, $m,r\ge1$, and $0<\alpha<1$, put
--   $$\lambda_j=\min\{1,E/j\},\qquad \Phi(E,K,d,\alpha)=\max_{1\le j\le K:\ \lambda_j>\alpha} j\,[1+d\log(\lambda_j/\alpha)].$$
--   Then, with constants depending only on $\delta$,
--   $$c_\delta\Phi\le B^\ast\le C_\delta\Phi .$$
--   In particular, for $\kappa_0=1/1024$,
--   $$B^\ast\asymp_\delta E[1+d(1-\alpha)]\quad(1-\kappa_0\le\alpha<1),\qquad B^\ast\asymp_\delta dK\log\Big(1+\frac E{K\alpha}\Big)\quad(0<\alpha\le1-\kappa_0).$$
--   For $\alpha\ge1$, $B^\ast=0$; for $\alpha=0$, no finite message suffices. For $r=0$, the output and comparator are zero, so $B^\ast=0$ at every nonnegative tolerance.
--
--   The maximization chooses how many directions can carry energy $\lambda_j$; the law covers all precisions, including the small improvement over the zero response near $\alpha=1$.
--
--   Differences from the source:
--   - encoding: c_δΦ ≤ B* ≤ C_δΦ and B* ≍_δ (…), with constants depending only on δ → c_δ, C_δ > 0 chosen after δ only; c_δ·X ≤ B for every achieving width and an achieving protocol of width ≤ C_δ·X; reason: two-part form of a least width; avoids the junk value of an infimum over an empty set
--   - encoding: B* = 0; no finite message suffices → a zero-bit achieving protocol exists; no protocol of any width achieves; reason: the meaning of the least width being zero or infinite
--   - reading: log in (242) and (244) → logarithm to base two; reason: §N.1 fixes base-two logarithms for the appendix; another base changes the bounds by a constant factor absorbed in c_δ, C_δ
-- source:
--   P. Xu, Information Required to Preserve Past Learning, STOC 2027 submission (held version, PDF sha256 48013ceb55cb5da782f256c3a4d1c95195bee48a2f4d0b2ed1e22bccd96d00fa), Theorem 20, p.67 (PDF p.69), eqs. (242)–(244); Appendix N, p.66 (PDF p.68), eqs. (240)–(241)

import Mathlib
import Definitions.Def_PreservePast_Supplement_SpectralAchieves

open MeasureTheory

namespace PreservePast.Supplement

/-- **Theorem 20 (Spectral-energy response law).** P. Xu, *Information Required to Preserve Past Learning*, STOC 2027 submission (held version,
PDF sha256 48013ceb…d00fa), Theorem 20, p.67 (PDF p.69),
eqs. (242)–(244).

Fix `0 < δ < 1/2`. For `d ≥ 2`, `1 ≤ E ≤ K ≤ d`, `m, r ≥ 1` and `0 < α < 1`:
(243) `c_δ Φ ≤ B* ≤ C_δ Φ`; (244) `B* ≍_δ E[1 + d(1−α)]` for `1 − κ₀ ≤ α < 1` and
`B* ≍_δ dK log(1 + E/(Kα))` for `0 < α ≤ 1 − κ₀`, `κ₀ = 1/1024`. For `α ≥ 1`, `B* = 0`; for
`α = 0` no finite message suffices; for `r = 0`, `B* = 0` at every nonnegative tolerance.

**Formalization Note.** `E` is real, `K, d, m, r` are natural numbers. The bounds on the least
width `B*` are stated in the two-part form of the published goal: a lower bound for every
achieving width (arbitrary public coins, coin spaces in `Type`) and an achieving protocol for
each upper bound; `B* = 0` is a zero-bit achieving protocol, and "no finite message suffices" is
that no width is achieved. The constants `c_δ, C_δ` are chosen after `δ` only. Logarithms are
base two (§N.1). The endpoint clauses are stated on the same parameter ranges
(`d ≥ 2`, `1 ≤ E ≤ K ≤ d`, `m ≥ 1`), with `r ≥ 1` for `α ≥ 1` and `α = 0`. -/
theorem theorem_20 :
    ∀ δ : ℝ, 0 < δ → δ < 1 / 2 → ∃ cδ Cδ : ℝ, 0 < cδ ∧ 0 < Cδ ∧
      ∀ (d K m r : ℕ) (E α : ℝ), 2 ≤ d → 1 ≤ E → E ≤ K → K ≤ d → 1 ≤ m →
        (1 ≤ r → 0 < α → α < 1 →
          ((∀ (B : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
              (enc : Matrix (Fin K) (Fin d) ℝ → Ω → Fin (2 ^ B))
              (dec : Fin (2 ^ B) → Ω → Matrix (Fin m) (Fin K) ℝ → Matrix (Fin m) (Fin d) ℝ),
              SpectralAchieves E r α δ P enc dec → cδ * spectralPhi E K d α ≤ (B : ℝ)) ∧
            ∃ B : ℕ, (B : ℝ) ≤ Cδ * spectralPhi E K d α ∧
              ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
              (enc : Matrix (Fin K) (Fin d) ℝ → Ω → Fin (2 ^ B))
              (dec : Fin (2 ^ B) → Ω → Matrix (Fin m) (Fin K) ℝ → Matrix (Fin m) (Fin d) ℝ), SpectralAchieves E r α δ P enc dec) ∧
          (1 - 1 / 1024 ≤ α →
            (∀ (B : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
              (enc : Matrix (Fin K) (Fin d) ℝ → Ω → Fin (2 ^ B))
              (dec : Fin (2 ^ B) → Ω → Matrix (Fin m) (Fin K) ℝ → Matrix (Fin m) (Fin d) ℝ),
              SpectralAchieves E r α δ P enc dec → cδ * (E * (1 + d * (1 - α))) ≤ (B : ℝ)) ∧
            ∃ B : ℕ, (B : ℝ) ≤ Cδ * (E * (1 + d * (1 - α))) ∧
              ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
              (enc : Matrix (Fin K) (Fin d) ℝ → Ω → Fin (2 ^ B))
              (dec : Fin (2 ^ B) → Ω → Matrix (Fin m) (Fin K) ℝ → Matrix (Fin m) (Fin d) ℝ), SpectralAchieves E r α δ P enc dec) ∧
          (α ≤ 1 - 1 / 1024 →
            (∀ (B : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
              (enc : Matrix (Fin K) (Fin d) ℝ → Ω → Fin (2 ^ B))
              (dec : Fin (2 ^ B) → Ω → Matrix (Fin m) (Fin K) ℝ → Matrix (Fin m) (Fin d) ℝ),
              SpectralAchieves E r α δ P enc dec →
              cδ * (d * K * Real.logb 2 (1 + E / (K * α))) ≤ (B : ℝ)) ∧
            ∃ B : ℕ, (B : ℝ) ≤ Cδ * (d * K * Real.logb 2 (1 + E / (K * α))) ∧
              ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
              (enc : Matrix (Fin K) (Fin d) ℝ → Ω → Fin (2 ^ B))
              (dec : Fin (2 ^ B) → Ω → Matrix (Fin m) (Fin K) ℝ → Matrix (Fin m) (Fin d) ℝ), SpectralAchieves E r α δ P enc dec)) ∧
        (1 ≤ r → 1 ≤ α →
          ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
            (enc : Matrix (Fin K) (Fin d) ℝ → Ω → Fin (2 ^ 0))
            (dec : Fin (2 ^ 0) → Ω → Matrix (Fin m) (Fin K) ℝ → Matrix (Fin m) (Fin d) ℝ),
            SpectralAchieves E r α δ P enc dec) ∧
        (1 ≤ r → α = 0 →
          ∀ (B : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
              (enc : Matrix (Fin K) (Fin d) ℝ → Ω → Fin (2 ^ B))
              (dec : Fin (2 ^ B) → Ω → Matrix (Fin m) (Fin K) ℝ → Matrix (Fin m) (Fin d) ℝ), ¬ SpectralAchieves E r α δ P enc dec) ∧
        (r = 0 → 0 ≤ α →
          ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
            (enc : Matrix (Fin K) (Fin d) ℝ → Ω → Fin (2 ^ 0))
            (dec : Fin (2 ^ 0) → Ω → Matrix (Fin m) (Fin K) ℝ → Matrix (Fin m) (Fin d) ℝ),
            SpectralAchieves E r α δ P enc dec) := by sorry

end PreservePast.Supplement
