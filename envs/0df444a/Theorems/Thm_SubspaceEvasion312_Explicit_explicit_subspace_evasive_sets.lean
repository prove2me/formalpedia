-- Prove2me | Theorems.Thm_SubspaceEvasion312_Explicit_explicit_subspace_evasive_sets
-- name    : SubspaceEvasion312.Explicit.explicit_subspace_evasive_sets
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:03:16.07227+00:00
-- url     : https://prove2.me/theorems/a58367e8-cca4-4754-847a-e7a9725b2816
-- title:
--   Theorem 24 — near-optimal explicit subspace evasive sets
-- statement:
--   There is one absolute polynomial degree $h$ with the following property. For every finite field $F_q$, every positive integer $r$, and every real $0<\varepsilon<1$, define
--
--   $$L(r,\varepsilon)=\min\!\left(2\left\lceil\frac{16r^2}{\varepsilon}\right\rceil,\;2\left\lceil\frac{256r(1+\log_2(r/\varepsilon))}{\varepsilon}\right\rceil\right).$$
--
--   For all sufficiently large ambient dimensions $N$, actual graph assemblies construct linearly $(r,L(r,\varepsilon))$ evasive sets $A_N\subseteq F_q^N$, with
--
--   $$|A_N|=q^{k_N}\ge q^{(1-\varepsilon)N},\qquad k_N=N-bM_N.$$
--
--   The local map is the defined deterministic conditional-expectation map, and the global map is its blockwise composition with a dimension-correct linear encoder. There is a fixed rational $\eta\in(3\varepsilon/4,\varepsilon)$ with $M_N=\lfloor\eta N/b\rfloor$, and a true indexed bijection using the canonical base-$q$ digits. Fixed construction and membership programs work at every $N\ge N_0$ in time $C(N+1)^h$, including setup. Their natural registers have the same polynomial value bound. The constants $C,N_0$ may depend on $q,r,\varepsilon$; $h$ and the intersection bound do not.
--
--   On the uniform asymptotic tail $r/\varepsilon\ge2$, the same full-domain construction satisfies
--
--   $$L(r,\varepsilon)\le1028\min\!\left(\frac{r^2}{\varepsilon},\frac{r\log_2(r/\varepsilon)}{\varepsilon}\right).$$
--
--   The theorem also exposes the introductory affine consequence: applying the same construction at rank $r+1$ yields affine $(r,L(r+1,\varepsilon))$ evasion with identical density and effective clauses. Its asymptotic multiplier can be taken as $4112$ on the same tail. No field, dimension, irrational value of $\varepsilon$, or branch of the minimum is omitted. These statements are open Lean proof obligations; compilation checks their types, not their proofs.
--
--   Differences from the source:
--   - reading: O(min(r²/ε,r log(r/ε)/ε)) without an explicit asymptotic tail → the full-parameter ceiling bound together with a uniform eventual bound for r/ε≥2, using log₂; reason: a global raw-log bound is impossible: q=2,r=1 and ε tending to one give L≥1 for every nonempty dense set, whereas K log(1/ε)/ε tends to zero for any fixed K; changing log base only changes the absolute multiplier
--   - generalization: the theorem states asymptotic intersection size; its proof gives ℓ_A and ℓ_B → both exact proof-derived ceiling bounds, plus the sufficient absolute witness 1028 and affine witness 4112; reason: these are additional quantitative information from the proof, preserve both branches and all parameters, and imply the source asymptotic order
--   - encoding: fixed real ε and the proof notation M=floor(εN/b) → a fixed rational η with 3ε/4<η<ε and M=floor(ηN/b), retaining density for the original real ε; reason: the strict local inequalities have slack: 10/(3/4)<16 and 100/(3/4)<256; finite rational advice avoids an exact-real oracle without restricting ε
--   - encoding: linear evasion in Definition 3 and affine evasion in the introduction → separate linear construction at r and affine consequence of the rank-r+1 construction; reason: every affine r-plane lies in a linear space of dimension at most r+1; no independent numbered milestone is invented
--   - encoding: constructable sets and polynomial membership time → actual graph ranges, dimension-correct encoders, canonical indexed bijections and uniform finite programs with charged preprocessing; reason: program existence and runtime bounds are conclusions, with one degree before all fields and parameters; no efficiency hypothesis or free global lookup table is assumed
-- source:
--   Brakensiek, Chen, Cheraghchi, Goyal, Guruswami, Putterman, Zhang, STOC 2027 submission #312 (October 2026), Theorem 24 and proof, printed p. 12 (PDF p. 13); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/312.pdf; PDF SHA256 a6946cb436bf453cfc53c1547fdd79e55134761b2192ee39f145dfc45490f6bc; Theorem 2 and Definition 3 affine comparison, printed p. 2 (PDF p. 3)

import Definitions.Def_SubspaceEvasion312_Explicit_construction

namespace SubspaceEvasion312.Explicit
/-- Theorem 24, printed p.12 (PDF p.13), with both ceiling estimates from
its proof and the introductory affine consequence at rank r+1. -/
theorem explicit_subspace_evasive_sets :
    ∃ degree : ℕ,
      (∀ (r : ℕ) (ε : ℝ), 0 < r → 0 < ε → ε < 1 → 2 ≤ (r : ℝ)/ε →
        (intersectionBound r ε : ℝ) ≤ 1028 * asymptoticShape r ε ∧
        (intersectionBound (r+1) ε : ℝ) ≤ 4112 * asymptoticShape r ε) ∧
      ∀ (F : Type) [Field F] [Fintype F] (r : ℕ) (ε : ℝ),
        0 < r → 0 < ε → ε < 1 →
        FixedFieldConstruction (F := F) r ε degree false ∧
        FixedFieldConstruction (F := F) (r+1) ε degree true := by sorry
end SubspaceEvasion312.Explicit
