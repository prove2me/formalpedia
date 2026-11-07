-- Prove2me | Theorems.Thm_SamplingLLL_lemma_A_6
-- name    : SamplingLLL.lemma_A_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:53:56.556193+00:00
-- url     : https://prove2.me/theorems/89555476-c533-4c26-b7ee-da2c785a542f
-- title:
--   Lemma A.6, (9)–(11), pp.22–23 — bidirectional packet circuit
-- statement:
--   Let $\mu,\pi$ be probability laws with an executable split $\mu=v\pi+\mu_{\mathrm{bad}}$, $v>0$ (9). For labels $z$, let $Q_z$ be a proposal measure on marks and $P_z$ a packet measure, both of mass $\omega_z$, with $\sum_z\omega_z\le B<1$, an unnormalized generator independent of the configuration returning $z$ with submeasure $Q_z$, the identity
--   $$
--   \mu_{\mathrm{bad}}+\sum_{z\in I^-}P_z=\sum_{z\in I^+}P_z \tag{10}
--   $$
--   with an executable coupling in both directions that retains labels, and balanced rows
--   $$
--   K^{\mathrm{in}}_z:[\Omega\times Z_z,\mu\otimes Q_z]\to[X_z,P_z],\qquad K^{\mathrm{out}}_z:[X_z,P_z]\to[\Omega,\omega_z\mu]. \tag{11}
--   $$
--   Then the forward and reverse kernels of the circuit are exact from $\mu$ to $\pi$ and from $\pi$ to $\mu$, and, excluding work internal to the generator and the rows, each uses an expected $2/v$ circuit passes.
--
--   Differences from the source:
--   - encoding: packet spaces $X_z$ with the physical projection, and "an executable coupling in both directions" → packets as configurations with the label retained alongside, and the coupling as the circuit's router, a kernel (deterministic or randomized) on labels at a fixed configuration, including the residual label, with (10) written label by label on each configuration in both directions; reason: a coupling that retains labels and the physical configuration is exactly such a pair of kernels; the mass form of (10) follows; the packets of the circuit are physical configurations, since the exit row is applied to the router's output
--   - encoding: "excluding work internal to the generator and packet rows" → the expected ticks when every row is free of ticks, since each pass flips one fair bit, charged one tick; reason: the pass count does not depend on the charges of the rows
-- source:
--   Achlioptas, Counting and Sampling by Local Repair: From the Lovász Local Lemma to Random k-SAT, STOC 2027 submission (manuscript sha256 7a943167…), Lemma A.6, eqs. (9)–(11), pp.22–23

import Mathlib
import Definitions.Def_SamplingLLL_Circuit

set_option autoImplicit false

open scoped ENNReal

namespace SamplingLLL

open Proc

/-- Lemma A.6 (Bidirectional packet circuit), with the hypotheses (9)–(11), pp.22–23. Exactness holds for
any rows with the stated laws. The pass count is read off the ticks of `forward`, `backward` when every row
is free of ticks, since each pass flips one fair bit, charged one tick ("excluding work internal to the
generator and packet rows").

Source: Achlioptas, STOC 2027 submission (manuscript sha256 7a943167…), Lemma A.6, eqs. (9)–(11), pp.22–23.

**Formalization Note.** Labels `T` carry marks in `M`; `Pk t` is the packet measure `P_z` projected to
`Ω`. The executable coupling in both directions is the router of the circuit, a kernel in `Proc` on
labels at a fixed physical configuration (deterministic or randomized): `C.route t` for a label `t`, and
`C.resid` for the residual label. (10) with its coupling is written label by label on each configuration:
forward, the router pushes `μ_bad` and the `I⁻` packets onto the `I⁺` packets; backward, it pushes the `I⁺`
packets onto the `I⁻` packets and `μ_bad`. The mass form of (10) follows. -/
theorem lemma_A_6 {Ω T M : Type} [Fintype Ω] [DecidableEq Ω] [Fintype T] [DecidableEq T] [Fintype M]
    (C : Circuit Ω T M) (μ π : Ω → ℝ) (good : Ω → Bool) (v B : ℝ)
    (Q : T → M → ℝ) (Pk : T → Ω → ℝ) (ω : T → ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1) (hπ : ∀ x, 0 ≤ π x) (hπ1 : ∑ x, π x = 1)
    (hv : 0 < v)
    -- the split (9), with `μ_bad = μ` off `good`
    (hsplit : ∀ x, μ x = v * π x + if good x then 0 else μ x)
    (hπgood : ∀ x, good x = false → π x = 0)
    (hQ : ∀ t k, 0 ≤ Q t k) (hPk : ∀ t x, 0 ≤ Pk t x)
    (hωQ : ∀ t, ω t = ∑ k, Q t k) (hωP : ∀ t, ω t = ∑ x, Pk t x)
    (hB : ∑ t, ω t ≤ B) (hB1 : B < 1)
    -- laws of the executable parts
    (hgood : ∀ x b, law (C.good x) b = if b = good x then 1 else 0)
    (hgenM : mass C.gen = 1)
    (hgen : ∀ t k, law C.gen (some (t, k)) = ENNReal.ofReal (Q t k))
    (hrouteM : ∀ t x, mass (C.route t x) = 1) (hresidM : ∀ x, mass (C.resid x) = 1)
    -- the balanced rows (11)
    (hin : ∀ t y, ∑ x, ∑ k, ENNReal.ofReal (μ x * Q t k) * law (C.enter t k x) y =
      ENNReal.ofReal (Pk t y))
    (hout : ∀ t y, ∑ x, ENNReal.ofReal (Pk t x) * law (C.exit t x) y = ENNReal.ofReal (ω t * μ y))
    (henterM : ∀ t k x, mass (C.enter t k x) = 1) (hexitM : ∀ t x, mass (C.exit t x) = 1)
    -- the identity (10) with its coupling, forward: `μ_bad + Σ_{I⁻} P_z` onto `Σ_{I⁺} P_z`
    (hfwd : ∀ y t', C.neg t' = false →
      ENNReal.ofReal (Pk t' y) =
        (if good y then 0 else ENNReal.ofReal (μ y)) * law (C.resid y) t' +
          ∑ t ∈ Finset.univ.filter (fun t => C.neg t = true),
            ENNReal.ofReal (Pk t y) * law (C.route t y) (some t'))
    (hfwdR : ∀ y t, good y = false → 0 < μ y → C.neg t = true → law (C.resid y) t = 0)
    (hfwdT : ∀ y t, C.neg t = true → 0 < Pk t y →
      law (C.route t y) none = 0 ∧ ∀ t', C.neg t' = true → law (C.route t y) (some t') = 0)
    -- the identity (10) with its coupling, backward: `Σ_{I⁺} P_z` onto `μ_bad + Σ_{I⁻} P_z`
    (hbwd : ∀ y t', C.neg t' = true →
      ENNReal.ofReal (Pk t' y) =
        ∑ t ∈ Finset.univ.filter (fun t => C.neg t = false),
          ENNReal.ofReal (Pk t y) * law (C.route t y) (some t'))
    (hbwdR : ∀ y, (if good y then 0 else ENNReal.ofReal (μ y)) =
      ∑ t ∈ Finset.univ.filter (fun t => C.neg t = false),
        ENNReal.ofReal (Pk t y) * law (C.route t y) none)
    (hbwdT : ∀ y t t', C.neg t = false → 0 < Pk t y → C.neg t' = false →
      law (C.route t y) (some t') = 0) :
    (∀ y, push μ C.forward y = ENNReal.ofReal (π y)) ∧
    (∀ y, push π C.backward y = ENNReal.ofReal (μ y)) ∧
    ((∀ x, TickFree (C.good x)) → TickFree C.gen → (∀ x, TickFree (C.resid x)) →
      (∀ t k x, TickFree (C.enter t k x)) → (∀ t x, TickFree (C.exit t x)) →
      (∀ t x, TickFree (C.route t x)) →
      ∑ x, ENNReal.ofReal (μ x) * expTicks (C.forward x) = ENNReal.ofReal (2 / v) ∧
      ∑ x, ENNReal.ofReal (π x) * expTicks (C.backward x) = ENNReal.ofReal (2 / v)) := by sorry

end SamplingLLL
