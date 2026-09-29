-- Prove2me | Theorems.Thm_WeierstrassCurve_threeFiveSwitchCurve
-- name    : WeierstrassCurve.threeFiveSwitchCurve
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/88c19125-05e5-53d0-9106-85f06047bda5
-- title:
--   The 3–5 switch for semistable integral models
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Z}$ (a tuple $a_1,\dots,a_6$ of integers) with $\Delta \neq 0$, satisfying the project's `IsSemistableModel`, which says that no prime $p$ dividing $\Delta$ divides $c_4$, and satisfying `W.ModRepIsIrreducible 5`, which is the project's notion `Affine.Point.GaloisRepIsIrreducible` for the base change of $W$ to $\mathbb{Q}$ and the algebraic closure $\overline{\mathbb{Q}}$ at $n = 5$: the $\mathbb{Z}$-torsion submodule $\{P : 5P = 0\}$ of the affine point group of $W$ over $\overline{\mathbb{Q}}$ is nontrivial, and every $\mathbb{Z}/5$-submodule of it stable under the action of every $\sigma \in \overline{\mathbb{Q}} \simeq_{\mathbb{Q}} \overline{\mathbb{Q}}$ (acting on points through the coordinatewise map) is $\bot$ or $\top$. The conclusion asserts the existence of a further Weierstrass curve $W'$ over $\mathbb{Z}$ with $\Delta' \neq 0$, again satisfying `IsSemistableModel`, with `W'.ModRepIsIrreducible 3` (the same irreducibility condition for the $3$-torsion, with $\mathbb{Z}/3$-submodules), and such that for every prime $\ell \neq 5$ with $\ell \nmid \Delta$ and $\ell \nmid \Delta'$ — this last pair of conditions being the project's `IsGoodPrimeFor` for $W$ and for $W'$, a statement about the given models and not about minimal models — one has $5 \mid a_\ell(W') - a_\ell(W)$ in $\mathbb{Z}$. Here $a_\ell$ of an integral model is `apOfModel`, namely $\ell + 1 - \#\,(W \bmod \ell)(\mathbb{Z}/\ell)$, the point count being the cardinality of the Mathlib affine point type of the reduction of the model modulo $\ell$ (which includes the point at infinity). Note that the statement records only the congruence between the traces, not any isomorphism between the $5$-torsion Galois modules of $W$ and $W'$.
--
--   This is the $3$–$5$ switch (the prime-switching argument) used by Wiles, in the form of Darmon–Diamond–Taylor, Lemma 3.49, with the auxiliary family of curves having prescribed mod-$5$ representation going back to Rubin–Silverberg. The formal statement is phrased entirely for integral Weierstrass models: semistability is the coprimality of $\Delta$ and $c_4$, a good prime means only that $\ell$ does not divide the discriminant of the given model, and the transfer of information from $W$ to $W'$ is packaged as the congruence $5 \mid a_\ell(W') - a_\ell(W)$ rather than as an isomorphism of residual representations. It feeds into [`WeierstrassCurve.modularity_of_semistableModel`](thm.html#WeierstrassCurve.modularity_of_semistableModel), where the case of reducible mod-$3$ representation is handled by proving modularity of $W'$ and then deducing residual modularity of $W$ mod $5$, and thence into [`FreyPackage.modularRepOfConductorLevel`](thm.html#FreyPackage.modularRepOfConductorLevel).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_threeFiveSwitchCurve.lean

import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_FLTPrelim_CofixedLine

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open CuspForm ModularFormClass UpperHalfPlane

theorem WeierstrassCurve.threeFiveSwitchCurve (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) (hW : W.IsSemistableModel) (h5 : W.ModRepIsIrreducible 5) : ∃ W' : WeierstrassCurve ℤ, W'.Δ ≠ 0 ∧ W'.IsSemistableModel ∧ W'.ModRepIsIrreducible 3 ∧ ∀ ℓ : ℕ, ℓ.Prime → W.IsGoodPrimeFor ℓ → W'.IsGoodPrimeFor ℓ → ℓ ≠ 5 → (5 : ℤ) ∣ (W'.apOfModel ℓ - W.apOfModel ℓ) := by sorry
