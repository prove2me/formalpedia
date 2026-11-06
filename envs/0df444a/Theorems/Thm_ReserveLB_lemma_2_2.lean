-- Prove2me | Theorems.Thm_ReserveLB_lemma_2_2
-- name    : ReserveLB.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:33:10.475193+00:00
-- url     : https://prove2.me/theorems/b9f23856-a4d4-47df-8a92-bbc1538722af
-- title:
--   Lemma 2.2 — reservation-preserving four-loss map onto smooth virtual classes
-- statement:
--   There is an algorithm running in time polynomial in the binary encoding of the speeds that, given positive rational speeds $s_1, \dots, s_m$ ($m \ge 1$), constructs virtual classes $C_0, \dots, C_{L-1}$ with speeds $S_h > 0$ and counts $N_h$, a forward map $F$ from original to virtual machines and a parent map $G$ from virtual to original machines, such that:
--   1. there are at most $2m^2$ virtual machines, and with $P_h = N_h S_h$, $A_h = \sum_{f \le h} P_f$,
--   $$
--   S_{h+1} \le S_h/2,\quad P_h \ge A_{h-1},\quad A_h \le 2P_h,\quad N_h \ge 2^h,\quad P_h/P_f \ge 2^{h-f-1}\ (f<h);\tag{1}
--   $$
--   2. every original schedule maps through $F$ with loss at most four: for every reservation $\sigma$ with nonempty sets and every size vector $x \ge 0$, $T_{F(\sigma)}(x) \le 4\,T_\sigma(x)$ on the virtual machines, and $|F(\sigma(j))| \le |\sigma(j)|$;
--   3. every virtual schedule lifts through $G$ with loss one: for every virtual reservation $\tau$ with nonempty sets and every $x \ge 0$, $T_{G(\tau)}(x) \le T_\tau(x)$ on the original machines, and $|G(\tau(j))| \le |\tau(j)|$.
--
--   The smoothing gives geometric class speeds while preserving the per-job reservation cap; it yields $B^* \le 4\,\mathrm{OPT}_k$ for the smoothed same-budget optimum.
--
--   Differences from the source:
--   - reading: Both maps preserve reservation set cardinalities → images do not increase cardinality: |F(σ(j))| ≤ |σ(j)| and |G(τ(j))| ≤ |τ(j)|; reason: the proof says "Set images cannot increase a reservation cap" (p.4); equality is false, since F sends all discarded originals to one endpoint
--   - reading: every original schedule maps through F with loss at most four; every virtual schedule lifts through G with loss one → T_{F(σ)}(x) ≤ 4 T_σ(x) and T_{G(τ)}(x) ≤ T_τ(x) for every reservation with nonempty sets and every size vector x ≥ 0; reason: a schedule is mapped machine by machine (proof, p.4), so the bounds hold pathwise; this gives B* ≤ 4 OPT_k (p.4)
--   - encoding: in polynomial bit time one can construct virtual machines, F and G → ∃ smooth with Turing.TM2ComputableInPolyTime encRatList encSmoothOut smooth; classes as a list (S_h, N_h); F as a list of (class, position); G as one parent list per class; virtual speeds S_h > 0 stated; reason: Mathlib's Turing-machine model; virtual machines have positive speeds (at least a/(2m), p.4)
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Lemma 2.2, (1), p.3; proof pp.3–4

import Mathlib
import Definitions.Def_ReserveLB_Tsig
import Definitions.Def_ReserveLB_ClassStr
import Definitions.Def_ReserveLB_ClassStr_VM
import Definitions.Def_ReserveLB_ClassStr_vspeed
import Definitions.Def_ReserveLB_ClassStr_Smooth1
import Definitions.Def_ReserveLB_ClassStr_ofList
import Definitions.Def_ReserveLB_encRatList
import Definitions.Def_ReserveLB_encSmoothOut
import Definitions.Def_OnlineCRS_Combine_Sym

namespace ReserveLB

/-- **Lemma 2.2 — reservation-preserving four-loss map.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Lemma 2.2, p.3: "In polynomial bit time one can construct at most 2m² virtual machines,
forward map F and parent map G, with classes C0, …, CL−1, speeds Sh, counts Nh, powers
Ph = NhSh, and prefixes Ah = Σ_(f≤h) Pf, such that Sh+1 ≤ Sh/2, Ph ≥ Ah−1, Ah ≤ 2Ph, Nh ≥ 2^h,
Ph/Pf ≥ 2^(h−f−1) (f < h). (1) Every original schedule maps through F with loss at most four.
Every virtual schedule lifts through G with loss one. Both maps preserve reservation set
cardinalities."

Some map `smooth`, computable by a Turing machine in time polynomial in the binary encoding of the
speed list, returns for every list of `m ≥ 1` positive speeds a class list `(S_h, N_h)`, a forward
map `F` (a virtual machine for every original) and a parent map `G` (an original for every virtual
machine) such that
1. every `S_h > 0`, the conditions (1) hold, and there are `Σ_h N_h ≤ 2m²` virtual machines;
2. for every reservation `σ` with nonempty sets and all sizes `x ≥ 0`,
   `T_(F(σ))(x) ≤ 4 T_σ(x)` on the virtual machines, and `|F(σ(j))| ≤ |σ(j)|`;
3. for every virtual reservation `τ` with nonempty sets and all `x ≥ 0`,
   `T_(G(τ))(x) ≤ T_τ(x)` on the originals, and `|G(τ(j))| ≤ |τ(j)|`.

**Formalization Note.** `F` and `G` are read from the output lists (`F` at index `i`, `G` at class
`h`, position `t`). "Preserve reservation set cardinalities" is read as "images do not increase
cardinality". The loss bounds hold for every size vector (pathwise). Polynomial time is
`Turing.TM2ComputableInPolyTime` with `encRatList`, `encSmoothOut`. -/
theorem lemma_2_2 :
    ∃ smooth : List ℚ → List (ℚ × ℕ) × List (ℕ × ℕ) × List (List ℕ),
      Nonempty (Turing.TM2ComputableInPolyTime encRatList encSmoothOut smooth) ∧
      ∀ s : List ℚ, s ≠ [] → (∀ a ∈ s, 0 < a) →
        (∀ h, 0 < (ClassStr.ofList (smooth s).1).S h) ∧
        (ClassStr.ofList (smooth s).1).Smooth1 ∧
        ∑ h, (ClassStr.ofList (smooth s).1).N h ≤ 2 * s.length ^ 2 ∧
        ∃ (F : Fin s.length → (ClassStr.ofList (smooth s).1).VM)
          (G : (ClassStr.ofList (smooth s).1).VM → Fin s.length),
          (∀ i, (smooth s).2.1.getD i.val (0, 0) = ((F i).1.val, (F i).2.val)) ∧
          (∀ v, ((smooth s).2.2.getD v.1.val []).getD v.2.val 0 = (G v).val) ∧
          (∀ (n : ℕ) (σ : Fin n → Finset (Fin s.length)), (∀ j, (σ j).Nonempty) →
            ∀ x : Fin n → ℝ, (∀ j, 0 ≤ x j) →
              Tsig (ClassStr.ofList (smooth s).1).vspeed (fun j => (σ j).image F) x ≤
                  4 * Tsig (fun i => ((s.get i : ℚ) : ℝ)) σ x ∧
                ∀ j, ((σ j).image F).card ≤ (σ j).card) ∧
          (∀ (n : ℕ) (τ : Fin n → Finset (ClassStr.ofList (smooth s).1).VM),
            (∀ j, (τ j).Nonempty) → ∀ x : Fin n → ℝ, (∀ j, 0 ≤ x j) →
              Tsig (fun i => ((s.get i : ℚ) : ℝ)) (fun j => (τ j).image G) x ≤
                  Tsig (ClassStr.ofList (smooth s).1).vspeed τ x ∧
                ∀ j, ((τ j).image G).card ≤ (τ j).card) := by sorry

end ReserveLB
