-- Prove2me | Theorems.Thm_PrivateRelease_VCLowerBound_lemma_3_13
-- name    : PrivateRelease.VCLowerBound.lemma_3_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T16:07:36.335869+00:00
-- url     : https://prove2.me/theorems/c5eaa944-fbbf-45d0-b2bd-2a4850d709fc
-- title:
--   Lemma 3.13 — a useful mechanism lets one reconstruct $T \in \mathcal D_S$ up to $|T'\Delta T| \le 2d\alpha$ with probability $1-\delta$
-- statement:
--   Let $S$ be a finite set of $d = 2m$ universe elements, $\mathcal D_S$ the family of its subsets of size $m$, and for each $T \in \mathcal D_S$ let $\varphi_T \in C$ be a predicate equal to the indicator of $T$ on $S$. Let $0 < \delta < 1$, and let $M$ be a mechanism on input databases of size $m$, with readout $\mathrm{ans}$, that is $(\alpha,\delta)$-useful for $C$.
--
--   Then for every $T \in \mathcal D_S$ and every input $z \in X^m$ that lists the elements of $T$, the reconstruction procedure $R$ (which returns a minimiser over $T' \in \mathcal D_S$ of $Q_{T'}(T') - \mathrm{ans}(o, \varphi_{T'})$) satisfies
--
--   $$\Pr_{o \sim M(z)}\big[\, |R(o) \,\Delta\, T| \le 2 d \alpha \,\big] \ \ge\ 1 - \delta .$$
--
--   This is the reconstruction attack: any mechanism that answers the queries $Q_T$ accurately reveals most of its input database. It is the step at which privacy will be contradicted.
--
--   **Formalization Note** The paper states the lemma for $\delta$ "bounded away from 1 by a constant"; the lemma holds for every $0 < \delta < 1$, so only that range is assumed; the constant bounding $\delta$ away from $1$ plays no role here. The procedure is the specific argmin of the paper's proof, with an arbitrary fixed tie-breaking rule. A set $T$ is given to $M$ as any injective listing $z$ of its elements; usefulness holds for every input, so the choice of listing does not matter.
-- source:
--   Blum, Ligett, Roth, A Learning Theory Approach to Non-Interactive Database Privacy, arXiv:1109.2229v1 (2011), pp. 11–12, Lemma 3.13 and its proof

import Mathlib
import Definitions.Def_PrivateRelease_VCLowerBound_Queries
import Definitions.Def_PrivateRelease_VCLowerBound_Construction

namespace PrivateRelease.VCLowerBound

open MeasureTheory

/-- Lemma 3.13 (pp. 11–12). Let `S` be a finite set of `d = 2m` universe elements, and for each
`T ∈ D_S` let `φ T ∈ C` be a predicate equal to the indicator of `T` on `S`. Let `M` be an
`(α, δ)`-useful mechanism for `C` on input databases of size `m`, with readout `ans`. Then for every
`T ∈ D_S` and every input `z` listing the elements of `T`, with probability at least `1 − δ` over
`o ∼ M(z)` the reconstruction procedure returns a set `T′ = reconstruct S m φ ans o` with
`|T′ Δ T| ≤ 2dα`, for every `0 < δ < 1` (the paper's "bounded away from 1" plays no role here). -/
theorem lemma_3_13 {X O : Type} [DecidableEq X] [MeasurableSpace O] (C : Set (X → Bool))
    (S : Finset X) (m : ℕ) (hS : S.card = 2 * m) (φ : Finset X → X → Bool)
    (hφC : ∀ T ∈ DS S m, φ T ∈ C) (hφ : ∀ T ∈ DS S m, IsIndicatorOn S T (φ T))
    (M : (Fin m → X) → Measure O) (ans : O → (X → Bool) → ℝ) (α δ : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hM : IsUseful C α δ M ans) (T : Finset X) (hT : T ∈ DS S m) (z : Fin m → X)
    (hz : IsEnum T z) :
    ENNReal.ofReal (1 - δ) ≤
      M z {o | ((symmDiff (reconstruct S m φ ans o) T).card : ℝ) ≤ 2 * (S.card : ℝ) * α} := by sorry

end PrivateRelease.VCLowerBound
